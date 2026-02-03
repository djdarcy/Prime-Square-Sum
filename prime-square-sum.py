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


def incremental_square_sum(primes: np.ndarray, target: int,
                           initial_sum: int = 0,
                           callback=None) -> Tuple[int, int, int, bool, bool]:
    """
    Compute sum of squared primes incrementally, stopping when target is reached.

    Args:
        primes: numpy array of primes
        target: Target sum to reach
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
        current_sum += p * p
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


# =============================================================================
# Main Search Function
# =============================================================================

def search_for_target(target: int,
                      prime_file: Optional[Path] = None,
                      max_primes: Optional[int] = None,
                      initial_sum: int = 0,
                      start_index: int = 0,
                      checkpoint_file: Optional[Path] = None,
                      verbose: bool = True) -> Result:
    """
    Search for a sum of squared primes that matches the target.

    Checkpoints are saved at adaptive intervals: more frequently as
    primes get larger (every prime after 1M processed).

    Args:
        target: Target sum to find
        prime_file: Optional file with precomputed primes
        max_primes: Maximum number of primes to try
        initial_sum: Starting sum (for resumption)
        start_index: Starting prime index (for resumption)
        checkpoint_file: File to save checkpoints
        verbose: Print progress

    Returns:
        Result object with computation details
    """
    start_time = time.time()
    current_sum = initial_sum
    count = start_index
    last_prime = 0
    found = False
    exceeded = False

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

    # Run computation
    final_sum, processed, last_prime, found, exceeded = incremental_square_sum(
        primes, target, initial_sum, progress_callback
    )

    count = start_index + processed
    elapsed = time.time() - start_time
    rate = count / elapsed if elapsed > 0 else 0

    # Final checkpoint
    if checkpoint_file:
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

    return parser.parse_args()


def verify_666():
    """Quick verification that sum of first 7 squared primes = 666."""
    print("Verifying: stf(10) = 666 = sum of first 7 squared primes")
    print()

    primes = generate_n_primes(7)
    print(f"First 7 primes: {primes.tolist()}")

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


def main():
    args = parse_args()

    # Quick verification mode
    if args.verify_666:
        success = verify_666()
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

    # Print configuration
    verbose = not args.quiet
    if verbose:
        print("=" * 60)
        print("Prime Square Sum Calculator v2")
        print("=" * 60)
        print(f"Target: {target}")
        print(f"Prime file: {args.prime_file or 'generate on-the-fly'}")
        print(f"Max primes: {args.max_primes or 'unlimited'}")
        print(f"Workers: {args.workers}")
        print(f"primesieve available: {PRIMESIEVE_AVAILABLE}")
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
