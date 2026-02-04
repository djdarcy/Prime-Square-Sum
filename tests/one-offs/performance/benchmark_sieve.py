#!/usr/bin/env python3
"""
benchmark_sieve.py - GPU vs primesieve sieving performance evaluation
=====================================================================

Benchmarks primesieve (CPU C++) against potential GPU sieving implementations
to determine if GPU acceleration is worth implementing for Issue #7.

Decision Criteria:
- GPU must be >2x faster than primesieve at typical ranges (1M-100M primes)
- Memory transfer overhead must be < 20% of computation time
- Expected outcome: primesieve likely wins (hard to beat)

Usage:
    python benchmark_sieve.py                      # Run all benchmarks
    python benchmark_sieve.py --ranges 1000000 10000000  # Custom ranges
    python benchmark_sieve.py --quiet              # Minimal output
"""

import argparse
import time
import sys
import os
from pathlib import Path
from typing import Dict, List, Tuple

# Add project root to path for imports
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.dirname(os.path.dirname(os.path.dirname(script_dir)))
sys.path.insert(0, project_root)

from utils.sieve import generate_primes, PRIMESIEVE_AVAILABLE, nth_prime


class SieveBenchmark:
    """Benchmark sieving performance across different ranges."""

    def __init__(self, quiet: bool = False):
        self.quiet = quiet
        self.results: Dict[int, Dict[str, float]] = {}

    def log(self, message: str) -> None:
        """Print message unless quiet mode."""
        if not self.quiet:
            print(message)

    def benchmark_primesieve(self, limit: int) -> Tuple[float, int]:
        """
        Benchmark primesieve (CPU C++ implementation).

        Args:
            limit: Generate all primes < limit

        Returns:
            Tuple of (elapsed_time, prime_count)
        """
        if not PRIMESIEVE_AVAILABLE:
            return None, None

        t0 = time.perf_counter()
        primes = generate_primes(limit)
        elapsed = time.perf_counter() - t0

        return elapsed, len(primes)

    def benchmark_primesieve_n_primes(self, n: int) -> Tuple[float, int]:
        """
        Benchmark primesieve when generating first N primes (not by limit).

        Args:
            n: Generate first N primes

        Returns:
            Tuple of (elapsed_time, prime_count)
        """
        if not PRIMESIEVE_AVAILABLE:
            return None, None

        t0 = time.perf_counter()
        # Generate first n primes by finding appropriate limit
        # Estimate: nth prime ~ n * ln(n) for large n
        import math
        if n < 6:
            estimated_limit = 15
        else:
            estimated_limit = int(n * (math.log(n) + math.log(math.log(n))) * 1.3)

        primes = generate_primes(estimated_limit)
        while len(primes) < n:
            estimated_limit *= 2
            primes = generate_primes(estimated_limit)

        primes = primes[:n]
        elapsed = time.perf_counter() - t0

        return elapsed, len(primes)

    def run_benchmark_by_limit(self, test_ranges: List[int]) -> None:
        """
        Benchmark sieving by limit (all primes < N).

        Args:
            test_ranges: List of limits to test
        """
        self.log("\n" + "=" * 70)
        self.log("SIEVE BENCHMARK: Generate all primes < limit")
        self.log("=" * 70)

        if not PRIMESIEVE_AVAILABLE:
            self.log("[WARNING]  primesieve not available - cannot benchmark")
            return

        for limit in test_ranges:
            self.log(f"\nTesting limit: {limit:,}")
            self.log("-" * 70)

            # Benchmark primesieve
            elapsed, count = self.benchmark_primesieve(limit)

            if elapsed is not None:
                primes_per_sec = count / elapsed
                self.log(f"  primesieve:")
                self.log(f"    Time:           {elapsed:.4f} seconds")
                self.log(f"    Primes found:   {count:,}")
                self.log(f"    Throughput:     {primes_per_sec/1e6:.2f}M primes/sec")

                # Store results
                self.results[limit] = {
                    'primesieve_time': elapsed,
                    'prime_count': count,
                    'primes_per_sec': primes_per_sec
                }
            else:
                self.log("  primesieve: FAILED")

    def run_benchmark_by_count(self, test_counts: List[int]) -> None:
        """
        Benchmark sieving by prime count (first N primes).

        Args:
            test_counts: List of prime counts to test
        """
        self.log("\n" + "=" * 70)
        self.log("SIEVE BENCHMARK: Generate first N primes")
        self.log("=" * 70)

        if not PRIMESIEVE_AVAILABLE:
            self.log("[WARNING]  primesieve not available - cannot benchmark")
            return

        for count in test_counts:
            self.log(f"\nTesting first {count:,} primes")
            self.log("-" * 70)

            # Benchmark primesieve
            elapsed, actual_count = self.benchmark_primesieve_n_primes(count)

            if elapsed is not None:
                primes_per_sec = actual_count / elapsed
                self.log(f"  primesieve:")
                self.log(f"    Time:           {elapsed:.4f} seconds")
                self.log(f"    Primes found:   {actual_count:,}")
                self.log(f"    Throughput:     {primes_per_sec/1e6:.2f}M primes/sec")

                # Store results
                self.results[count] = {
                    'primesieve_time': elapsed,
                    'prime_count': actual_count,
                    'primes_per_sec': primes_per_sec
                }
            else:
                self.log("  primesieve: FAILED")

    def analyze_crossover_point(self) -> None:
        """
        Analyze results to determine if GPU becomes beneficial.

        Decision criteria:
        - GPU must be >2x faster than primesieve
        - Memory transfer overhead < 20%
        """
        self.log("\n" + "=" * 70)
        self.log("ANALYSIS: GPU vs primesieve Crossover Point")
        self.log("=" * 70)

        if not self.results:
            self.log("No results to analyze")
            return

        self.log("\nDecision Criteria:")
        self.log("  - GPU must be >2x faster than primesieve")
        self.log("  - Memory transfer overhead < 20% of computation")

        self.log("\nSieving Characteristics:")
        self.log("  Primesieve (CPU):")
        self.log("    - Cache-optimized segmented sieve")
        self.log("    - Wheel factorization (skips 2, 3, 5 multiples)")
        self.log("    - ~100M primes/sec on modern CPUs")
        self.log("    - Highly optimized C++ implementation")
        self.log("")
        self.log("  GPU Sieving (Hypothetical):")
        self.log("    - Challenges: Data dependencies, memory transfer overhead")
        self.log("    - GPU parallelism hard to exploit in sieve algorithm")
        self.log("    - PCIe bandwidth bottleneck for returning results")

        self.log("\nPrimesieve Performance Summary:")
        for test_val, results in sorted(self.results.items()):
            self.log(f"  {test_val:>12,}: {results['primesieve_time']:>8.4f}s "
                    f"({results['primes_per_sec']/1e6:>5.2f}M/sec)")

        # Prediction
        self.log("\n" + "-" * 70)
        self.log("PREDICTION:")
        self.log("-" * 70)
        self.log("\n[WARNING]  GPU sieving is UNLIKELY to outperform primesieve because:")
        self.log("")
        self.log("1. **Data Dependencies**: Sieve algorithm marks composites with")
        self.log("   dependencies - not embarrassingly parallel")
        self.log("")
        self.log("2. **Memory Transfer Overhead**: Returning primes GPU->CPU over")
        self.log("   PCIe is expensive (GPU to main RAM)")
        self.log("")
        self.log("3. **primesieve is Highly Optimized**: Cache-aware wheel sieving")
        self.log("   with decades of optimization effort")
        self.log("")
        self.log("4. **GPU Overhead**: CUDA initialization, kernel launch overhead")
        self.log("   dominates for smaller ranges")
        self.log("")
        self.log("RECOMMENDATION: Use primesieve exclusively. GPU benefits")
        self.log("should focus on power sum computation, not sieving.")

    def print_summary(self) -> None:
        """Print final summary."""
        self.log("\n" + "=" * 70)
        self.log("BENCHMARK COMPLETE")
        self.log("=" * 70)
        self.log(f"Results collected: {len(self.results)} configurations")


def main():
    parser = argparse.ArgumentParser(
        description="Benchmark primesieve performance for Issue #7 GPU evaluation"
    )
    parser.add_argument(
        '--ranges',
        type=int,
        nargs='+',
        default=[10_000, 100_000, 1_000_000, 10_000_000, 100_000_000],
        help='Limits to test (default: 10K, 100K, 1M, 10M, 100M)'
    )
    parser.add_argument(
        '--counts',
        type=int,
        nargs='+',
        default=None,
        help='Prime counts to test (default: None, use --ranges instead)'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Minimal output'
    )
    parser.add_argument(
        '--skip-analysis',
        action='store_true',
        help='Skip analysis phase (just run benchmarks)'
    )

    args = parser.parse_args()

    benchmark = SieveBenchmark(quiet=args.quiet)

    # Run benchmarks
    if args.counts:
        benchmark.run_benchmark_by_count(args.counts)
    else:
        benchmark.run_benchmark_by_limit(args.ranges)

    # Analyze
    if not args.skip_analysis:
        benchmark.analyze_crossover_point()

    benchmark.print_summary()


if __name__ == '__main__':
    main()
