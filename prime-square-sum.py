#!/usr/bin/env python3
"""
prime-square-sum.py - Optimized Prime Square Sum Calculator
=============================================================

Calculates the sum of squared primes to verify the conjecture:
    stf(b) = sum of squared primes for certain triangular bases?

Known: stf(10) = 666 = 2² + 3² + 5² + 7² + 11² + 13² + 17²

This version features:
    - Python 3 (modern, maintained)
    - primesieve library (fastest known sieve)
    - NumPy for efficient array operations
    - Multiprocessing for CPU parallelism
    - Backward compatibility with legacy pickle files
    - Resumable computation via checkpoints

Usage:
    # Verify stf(10) = 666
    python prime-square-sum.py --target 666 --max-primes 100

    # Search for sum matching stf(666)
    python prime-square-sum.py --target 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290

    # Use precomputed primes
    python prime-square-sum.py --prime-file primes.npy --target 666

    # Resume from checkpoint
    python prime-square-sum.py --resume checkpoint.json --target <target>

Author: D. Darcy
Project: https://github.com/djdarcy/Prime-Square-Sum
Related: Zero_AG to The Scarcity Framework (Way-of-Scarcity/papers)
"""

import argparse
import json
import numpy as np
import signal
import sys
import time
from dataclasses import dataclass, asdict
from multiprocessing import Pool, cpu_count
from pathlib import Path
from typing import Optional, Tuple, List

# Version
VERSION_FILE = Path(__file__).parent / "VERSION"
__version__ = VERSION_FILE.read_text().strip() if VERSION_FILE.exists() else "2.0.0"

# Local imports
from utils.sieve import generate_primes, generate_n_primes, nth_prime, PRIMESIEVE_AVAILABLE
from utils.prime_io import load_primes, save_primes, load_primes_range
from utils import gpu as gpu_utils
from utils.sum_cache import IncrementalSumCache


# =============================================================================
# Data Structures
# =============================================================================

@dataclass
class ComputationState:
    """Checkpoint state for resumable computation."""
    target: str                    # Target sum (string for arbitrary precision)
    current_sum: str               # Current partial sum
    primes_processed: int          # Number of primes processed
    last_prime: int                # Last prime processed
    start_time: float              # When computation started
    elapsed_time: float            # Total elapsed time
    found: bool                    # Whether target was found
    exceeded: bool                 # Whether we exceeded target

    def to_json(self, filepath: Path) -> None:
        """Save state to JSON file."""
        with open(filepath, 'w') as f:
            json.dump(asdict(self), f, indent=2)

    @classmethod
    def from_json(cls, filepath: Path) -> 'ComputationState':
        """Load state from JSON file."""
        with open(filepath, 'r') as f:
            data = json.load(f)
        return cls(**data)


@dataclass
class Result:
    """Final computation result."""
    target: int
    final_sum: int
    primes_count: int
    last_prime: int
    match: bool
    exceeded: bool
    elapsed_seconds: float
    primes_per_second: float


# =============================================================================
# Core Computation
# =============================================================================

def get_checkpoint_interval(count: int) -> int:
    """
    Return adaptive checkpoint interval based on primes processed.

    As primes get larger, they become more expensive to compute,
    so we save more frequently to avoid losing progress.

    Args:
        count: Number of primes processed so far

    Returns:
        How often to checkpoint (every N primes)
    """
    if count < 10_000:
        return 1_000       # Every 1k for first 10k
    elif count < 100_000:
        return 100         # Every 100 up to 100k
    elif count < 1_000_000:
        return 10          # Every 10 up to 1M
    else:
        return 1           # Every prime after 1M


def square_sum_chunk(primes: np.ndarray) -> int:
    """
    Compute sum of squared primes for a chunk.

    Uses Python int for arbitrary precision accumulation.

    Args:
        primes: numpy array of primes

    Returns:
        Sum of p² for all p in primes
    """
    # Convert to Python ints for arbitrary precision
    return sum(int(p) ** 2 for p in primes)


def parallel_square_sum(primes: np.ndarray, num_workers: Optional[int] = None,
                        chunk_size: int = 100_000) -> int:
    """
    Compute sum of squared primes using multiprocessing.

    Args:
        primes: numpy array of primes
        num_workers: Number of worker processes (default: CPU count)
        chunk_size: Size of chunks for parallel processing

    Returns:
        Sum of p² for all primes
    """
    if num_workers is None:
        num_workers = cpu_count()

    # For small arrays, don't bother with parallelism
    if len(primes) < chunk_size:
        return square_sum_chunk(primes)

    # Split into chunks
    chunks = [primes[i:i + chunk_size] for i in range(0, len(primes), chunk_size)]

    # Process in parallel
    with Pool(processes=num_workers) as pool:
        partial_sums = pool.map(square_sum_chunk, chunks)

    # Accumulate with arbitrary precision
    return sum(partial_sums)


def incremental_sum(primes: np.ndarray, target: int, power: int = 2,
                    initial_sum: int = 0,
                    callback=None) -> Tuple[int, int, int, bool, bool]:
    """
    Compute sum of primes raised to power incrementally, stopping when target is reached.

    Args:
        primes: numpy array of primes
        target: Target sum to reach
        power: Exponent to raise each prime to (default: 2)
        initial_sum: Starting sum (for resumption)
        callback: Optional callback(count, current_sum, last_prime) for progress

    Returns:
        Tuple of (final_sum, count, last_prime, found_exact, exceeded)
    """
    current_sum = initial_sum
    count = 0
    last_prime = 0
    next_checkpoint = get_checkpoint_interval(0)

    for p in primes:
        p = int(p)
        current_sum += p ** power
        count += 1
        last_prime = p

        if callback and count >= next_checkpoint:
            callback(count, current_sum, last_prime)
            next_checkpoint = count + get_checkpoint_interval(count)

        if current_sum == target:
            return current_sum, count, last_prime, True, False
        elif current_sum > target:
            return current_sum, count, last_prime, False, True

    return current_sum, count, last_prime, False, False


def incremental_square_sum(primes: np.ndarray, target: int,
                           initial_sum: int = 0,
                           callback=None) -> Tuple[int, int, int, bool, bool]:
    """
    Compute sum of squared primes incrementally, stopping when target is reached.

    Convenience wrapper for incremental_sum with power=2.

    Args:
        primes: numpy array of primes
        target: Target sum to reach
        initial_sum: Starting sum (for resumption)
        callback: Optional callback(count, current_sum, last_prime) for progress

    Returns:
        Tuple of (final_sum, count, last_prime, found_exact, exceeded)
    """
    return incremental_sum(primes, target, power=2, initial_sum=initial_sum, callback=callback)


# =============================================================================
# Main Search Function
# =============================================================================

def search_for_target(target: int,
                      prime_file: Optional[Path] = None,
                      max_primes: Optional[int] = None,
                      power: int = 2,
                      use_cache: bool = False,
                      cache_file: Optional[Path] = None,
                      initial_sum: int = 0,
                      start_index: int = 0,
                      checkpoint_file: Optional[Path] = None,
                      verbose: bool = True) -> Result:
    """
    Search for a sum of primes (raised to power) that matches the target.

    Supports both batch computation and incremental caching for multi-target searches.
    Checkpoints are saved at adaptive intervals: more frequently as
    primes get larger (every prime after 1M processed).

    Args:
        target: Target sum to find
        prime_file: Optional file with precomputed primes
        max_primes: Maximum number of primes to try
        power: Exponent to raise primes to (default: 2)
        use_cache: Enable incremental sum caching (O(1) per prime)
        cache_file: Path to cache file (default: data/cache/sums.npz)
        initial_sum: Starting sum (for resumption)
        start_index: Starting prime index (for resumption)
        checkpoint_file: File to save checkpoints
        verbose: Print progress

    Returns:
        Result object with computation details
    """
    start_time = time.time()
    found = False
    exceeded = False

    # Set up cache if requested
    cache = None
    if use_cache:
        cache_file = cache_file or Path("data/cache/sums.npz")
        if cache_file.exists():
            if verbose:
                print(f"Loading cache from {cache_file}...")
            try:
                cache = IncrementalSumCache.load_checkpoint(cache_file)
                if power not in cache.metadata.powers:
                    # Power not in cache, reload with new power added
                    current_sum = cache.get_sum(2) if 2 in cache.metadata.powers else 0
                    cache = IncrementalSumCache(powers=cache.metadata.powers + [power])
                    cache.add_prime(2)  # Reinitialize
                else:
                    current_sum = cache.get_sum(power)
                if verbose:
                    print(f"Loaded cache: {cache.get_prime_count()} primes, last={cache.get_last_prime()}")
            except Exception as e:
                if verbose:
                    print(f"Failed to load cache ({e}), creating new cache")
                cache = IncrementalSumCache(powers=[power])
                current_sum = 0
        else:
            if verbose:
                print(f"Cache not found, creating new cache: {cache_file}")
            cache = IncrementalSumCache(powers=[power])
            current_sum = 0

        count = cache.get_prime_count()
        last_prime = cache.get_last_prime()
    else:
        current_sum = initial_sum
        count = start_index
        last_prime = 0

    # Load or generate primes
    if prime_file and prime_file.exists():
        if verbose:
            print(f"Loading primes from {prime_file}...")
        primes = load_primes(prime_file)
        if start_index > 0:
            primes = primes[start_index:]
        if max_primes:
            primes = primes[:max_primes]
        if verbose:
            print(f"Loaded {len(primes):,} primes")
    else:
        if max_primes:
            if verbose:
                print(f"Generating first {max_primes:,} primes...")
            primes = generate_n_primes(max_primes)
        else:
            # Estimate how many primes we might need
            # Very rough: if target is T, we need roughly T^(1/2) primes
            # But this is a vast underestimate for large T
            if verbose:
                print("Generating primes (will stop when target reached)...")
            # Start with 1 million, expand if needed
            primes = generate_n_primes(1_000_000)

        if verbose:
            print(f"Generated {len(primes):,} primes")

    # Progress callback (called at adaptive intervals)
    def progress_callback(n, s, p):
        nonlocal count, current_sum, last_prime
        count = start_index + n
        current_sum = s
        last_prime = p

        elapsed = time.time() - start_time
        rate = n / elapsed if elapsed > 0 else 0

        if verbose:
            pct = (s / target * 100) if target > 0 else 0
            print(f"  Processed: {count:,} primes | "
                  f"Sum: {s:,} ({pct:.6f}% of target) | "
                  f"Rate: {rate:,.0f} primes/sec")

        # Save checkpoint
        if checkpoint_file:
                state = ComputationState(
                    target=str(target),
                    current_sum=str(s),
                    primes_processed=count,
                    last_prime=p,
                    start_time=start_time,
                    elapsed_time=elapsed,
                    found=False,
                    exceeded=False
                )
                state.to_json(checkpoint_file)

    # Use cache path if enabled, otherwise use batch incremental sum
    if cache:
        # Incremental caching path
        next_checkpoint = get_checkpoint_interval(cache.get_prime_count())

        for prime in primes:
            prime = int(prime)

            # Skip primes already in cache
            if prime <= cache.get_last_prime():
                continue

            cache.add_prime(prime)
            current_sum = cache.get_sum(power)
            count = cache.get_prime_count()
            last_prime = prime

            # Progress callback at checkpoint intervals
            if count >= next_checkpoint:
                progress_callback(count - start_index, current_sum, prime)
                next_checkpoint = count + get_checkpoint_interval(count)

                # Save cache checkpoint
                if cache.should_checkpoint():
                    cache.save_checkpoint(cache_file)

            # Check target
            if current_sum == target:
                found = True
                break
            elif current_sum > target:
                exceeded = True
                break

        # Final cache save
        cache.save_checkpoint(cache_file)

        final_sum = current_sum
        processed = count - start_index
    else:
        # Batch computation path (original behavior)
        final_sum, processed, last_prime, found, exceeded = incremental_sum(
            primes, target, power=power, initial_sum=initial_sum, callback=progress_callback
        )
        count = start_index + processed

    elapsed = time.time() - start_time
    rate = count / elapsed if elapsed > 0 else 0

    # Final checkpoint (batch path only)
    if checkpoint_file and not cache:
        state = ComputationState(
            target=str(target),
            current_sum=str(final_sum),
            primes_processed=count,
            last_prime=last_prime,
            start_time=start_time,
            elapsed_time=elapsed,
            found=found,
            exceeded=exceeded
        )
        state.to_json(checkpoint_file)

    return Result(
        target=target,
        final_sum=final_sum,
        primes_count=count,
        last_prime=last_prime,
        match=found,
        exceeded=exceeded,
        elapsed_seconds=elapsed,
        primes_per_second=rate
    )


# =============================================================================
# CLI Interface
# =============================================================================

def parse_args():
    parser = argparse.ArgumentParser(
        description="Calculate sum of squared primes to find target value",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Verify stf(10) = 666 (sum of first 7 squared primes)
  python prime-square-sum.py --target 666 --max-primes 100

  # Search using precomputed primes
  python prime-square-sum.py --prime-file primes.npy --target 666

  # Resume from checkpoint
  python prime-square-sum.py --resume checkpoint.json

Known values:
  stf(10) = 666 = 2² + 3² + 5² + 7² + 11² + 13² + 17² (7 primes)
        """
    )

    parser.add_argument(
        '--target', '-t',
        type=str,
        help="Target sum to search for (supports arbitrary precision)"
    )

    parser.add_argument(
        '--prime-file', '-f',
        type=Path,
        help="File containing precomputed primes (.npy, .pkl, .dat, .txt)"
    )

    parser.add_argument(
        '--max-primes', '-n',
        type=int,
        help="Maximum number of primes to process"
    )

    parser.add_argument(
        '--workers', '-w',
        type=int,
        default=cpu_count(),
        help=f"Number of worker processes (default: {cpu_count()})"
    )

    parser.add_argument(
        '--checkpoint', '-c',
        type=Path,
        default=Path("checkpoint.json"),
        help="Checkpoint file for resumable computation"
    )

    parser.add_argument(
        '--resume', '-r',
        type=Path,
        help="Resume from checkpoint file"
    )

    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help="Suppress progress output"
    )

    parser.add_argument(
        '--verify-666',
        action='store_true',
        help="Quick verification that stf(10) = 666"
    )

    parser.add_argument(
        '--power', '-p',
        type=int,
        default=2,
        help="Power to raise primes to (default: 2 for squares)"
    )

    parser.add_argument(
        '--no-cache',
        action='store_true',
        help="Disable incremental sum caching (default: caching enabled)"
    )

    parser.add_argument(
        '--cache-file',
        type=Path,
        default=Path("data/cache/sums.npz"),
        help="Cache file location (default: data/cache/sums.npz)"
    )

    parser.add_argument(
        '--no-gpu',
        action='store_true',
        help="Disable GPU acceleration (use CPU only)"
    )

    return parser.parse_args()


def verify_666(use_gpu: bool = True):
    """Quick verification that sum of first 7 squared primes = 666."""
    print("Verifying: stf(10) = 666 = sum of first 7 squared primes")
    print()

    primes = generate_n_primes(7)
    print(f"First 7 primes: {primes.tolist()}")

    # Use GPU if available
    if use_gpu and gpu_utils.GPU_AVAILABLE:
        total = gpu_utils.power_sum(primes, power=2, use_gpu=True)
        print(f"Sum (GPU): {total}")
    else:
        squares = [int(p)**2 for p in primes]
        print(f"Squares: {squares}")
        total = sum(squares)
        print(f"Sum: {' + '.join(map(str, squares))} = {total}")

    print()

    if total == 666:
        print("VERIFIED: stf(10) = 666")
        return True
    else:
        print(f"FAILED: Expected 666, got {total}")
        return False


def gpu_bulk_sum(primes: np.ndarray, power: int = 2) -> int:
    """
    Compute sum of primes raised to power using GPU.

    This is for bulk computation - no incremental target checking.
    """
    if gpu_utils.GPU_AVAILABLE:
        return gpu_utils.power_sum(primes, power=power, use_gpu=True)
    else:
        return gpu_utils.power_sum(primes, power=power, use_gpu=False)


def main():
    args = parse_args()

    # Quick verification mode
    if args.verify_666:
        gpu_utils.init_gpu()  # Try to initialize GPU for verification
        success = verify_666(use_gpu=not args.no_gpu)
        sys.exit(0 if success else 1)

    # Resume from checkpoint
    if args.resume:
        if not args.resume.exists():
            print(f"Error: Checkpoint file not found: {args.resume}")
            sys.exit(1)

        state = ComputationState.from_json(args.resume)
        target = int(state.target)
        initial_sum = int(state.current_sum)
        start_index = state.primes_processed

        print(f"Resuming from checkpoint:")
        print(f"  Target: {target}")
        print(f"  Current sum: {initial_sum}")
        print(f"  Primes processed: {start_index:,}")
        print()
    else:
        if not args.target:
            print("Error: --target is required (or use --verify-666)")
            sys.exit(1)

        target = int(args.target)
        initial_sum = 0
        start_index = 0

    # Initialize GPU
    use_gpu = not args.no_gpu
    if use_gpu:
        gpu_utils.init_gpu()

    # Print configuration
    verbose = not args.quiet
    if verbose:
        print("=" * 60)
        print(f"Prime Power Sum Calculator v{__version__}")
        print("=" * 60)
        print(f"Target: {target}")
        print(f"Power: {args.power} (computing sum of p^{args.power})")
        print(f"Prime file: {args.prime_file or 'generate on-the-fly'}")
        print(f"Max primes: {args.max_primes or 'unlimited'}")
        print(f"Caching: {'Disabled' if args.no_cache else 'Enabled (default)'}")
        if not args.no_cache:
            print(f"Cache file: {args.cache_file}")
        if gpu_utils.GPU_AVAILABLE and use_gpu:
            gpu_utils.print_gpu_status()
        else:
            print(f"GPU: {'Disabled' if args.no_gpu else 'Not available'}")
            print(f"CPU Workers: {args.workers}")
        print(f"primesieve: {'Available' if PRIMESIEVE_AVAILABLE else 'Not available (using fallback)'}")
        print("=" * 60)
        print()

    # Set up signal handler for graceful interruption
    def signal_handler(sig, frame):
        print("\nInterrupted! Checkpoint saved.")
        sys.exit(0)

    signal.signal(signal.SIGINT, signal_handler)

    # Run search
    result = search_for_target(
        target=target,
        prime_file=args.prime_file,
        max_primes=args.max_primes,
        power=args.power,
        use_cache=not args.no_cache,
        cache_file=args.cache_file,
        initial_sum=initial_sum,
        start_index=start_index,
        checkpoint_file=args.checkpoint,
        verbose=verbose
    )

    # Print result
    print()
    print("=" * 60)
    print("RESULT")
    print("=" * 60)
    print(f"Target:        {result.target}")
    print(f"Final sum:     {result.final_sum}")
    print(f"Primes used:   {result.primes_count:,}")
    print(f"Last prime:    {result.last_prime:,}")
    print(f"Elapsed:       {result.elapsed_seconds:.2f} seconds")
    print(f"Rate:          {result.primes_per_second:,.0f} primes/second")
    print()

    if result.match:
        print(f"MATCH FOUND!")
        print(f"Target {target} = sum of first {result.primes_count} squared primes")
    elif result.exceeded:
        print(f"TARGET EXCEEDED")
        print(f"Sum exceeded target at prime #{result.primes_count} ({result.last_prime})")
        print(f"Overshoot: {result.final_sum - result.target}")
    else:
        print(f"TARGET NOT REACHED")
        print(f"Need more primes to continue search")

    print("=" * 60)

    return 0 if result.match else 1


if __name__ == "__main__":
    sys.exit(main())
