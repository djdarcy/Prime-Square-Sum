#!/usr/bin/env python3
"""
memory_sieve.py - Memory requirements analysis for sieve algorithms
====================================================================

Analyzes memory usage of the Sieve of Eratosthenes for different use cases:
1. Finding all primes up to a limit
2. Finding the first N primes (using Prime Number Theorem estimate)

This helps understand when the Python fallback is acceptable vs when
primesieve (with its segmented sieve) is necessary.

Usage:
    python memory_sieve.py
    python memory_sieve.py --verify    # Also verify sieve correctness

Related: Issue #12 (Pre-filter benchmark)
"""

import argparse
import math
import sys
import os

# Add project root to path for imports
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.dirname(os.path.dirname(os.path.dirname(script_dir)))
sys.path.insert(0, project_root)


def format_bytes(bytes_needed: int) -> str:
    """Format bytes as human-readable string."""
    if bytes_needed < 1024:
        return f'{bytes_needed} B'
    elif bytes_needed < 1024**2:
        return f'{bytes_needed/1024:.1f} KB'
    elif bytes_needed < 1024**3:
        return f'{bytes_needed/1024**2:.1f} MB'
    else:
        return f'{bytes_needed/1024**3:.2f} GB'


def analyze_memory_by_limit():
    """Analyze memory for finding all primes up to a limit."""
    print('Memory Usage: All primes up to limit')
    print('=' * 60)
    print()
    print('Our fallback uses np.ones(limit, dtype=bool)')
    print('NumPy bool = 1 byte per element')
    print()

    limits = [10_000, 100_000, 1_000_000, 10_000_000, 100_000_000, 1_000_000_000]

    print(f'{"Limit":>15} | {"Array Size":>12} | {"Memory":>10}')
    print('-' * 45)

    for limit in limits:
        bytes_needed = limit * 1  # 1 byte per bool
        mem_str = format_bytes(bytes_needed)
        print(f'{limit:>15,} | {limit:>12,} | {mem_str:>10}')

    print()


def analyze_memory_by_n_primes():
    """Analyze memory for finding first N primes."""
    print('Memory Usage: First N primes (typical primesum use case)')
    print('=' * 60)
    print()
    print('generate_n_primes() uses Prime Number Theorem to estimate limit')
    print('The nth prime is approximately n * ln(n)')
    print()

    n_values = [1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000]

    print(f'{"N primes":>12} | {"Est. limit":>15} | {"Memory (fallback)":>18}')
    print('-' * 55)

    for n in n_values:
        if n < 6:
            limit = 15
        else:
            ln_n = math.log(n)
            limit = int(n * (ln_n + math.log(ln_n)) * 1.3)  # 1.3 safety factor

        mem_bytes = limit * 1
        mem_str = format_bytes(mem_bytes)
        print(f'{n:>12,} | {limit:>15,} | {mem_str:>18}')

    print()
    print('Key insight: To get N primes, we sieve up to ~N*ln(N), not N')
    print('             So 1M primes needs ~20 MB, not 1 GB')
    print()


def explain_primesieve_optimizations():
    """Explain why primesieve uses less memory."""
    print('Primesieve optimizations (why it uses less memory)')
    print('=' * 60)
    print()
    print('1. Segmented sieve: processes in cache-sized chunks (~32KB)')
    print('   - Only needs memory for one segment at a time')
    print('   - Can handle arbitrarily large ranges')
    print()
    print('2. Bit array: 1 bit per number (8x reduction)')
    print('   - 1 GB range -> 125 MB')
    print()
    print('3. Wheel factorization: skip multiples of 2, 3, 5')
    print('   - Only store candidates not divisible by small primes')
    print('   - Additional ~3x reduction')
    print()
    print('4. Combined: ~50x less memory than naive bool array')
    print()


def verify_sieve_correctness():
    """Verify Python sieve matches primesieve."""
    import numpy as np
    from utils.sieve import _python_sieve, PRIMESIEVE_AVAILABLE

    print('Verification: Python sieve correctness')
    print('=' * 60)
    print()

    test_limits = [100, 1000, 10000, 100000]

    if PRIMESIEVE_AVAILABLE:
        import primesieve
        print('Comparing against primesieve (gold standard)')
        print()

        all_match = True
        for limit in test_limits:
            our_primes = _python_sieve(limit)
            reference = np.array(primesieve.primes(limit), dtype=np.int64)
            match = np.array_equal(our_primes, reference)
            status = 'OK' if match else 'MISMATCH'
            print(f'  limit={limit:>6}: {len(our_primes):>5} primes - {status}')
            if not match:
                all_match = False

        print()
        if all_match:
            print('All tests passed - sieve is correct')
        else:
            print('WARNING: Some tests failed!')
    else:
        print('primesieve not available - cannot verify')
        print('Run: conda install -c conda-forge python-primesieve')

    print()


def explain_sqrt_optimization():
    """Explain why we only iterate to sqrt(limit)."""
    print('Why sqrt(limit) is sufficient (no primes missed)')
    print('=' * 60)
    print()
    print('Mathematical proof:')
    print('  If n is composite, it has a prime factor <= sqrt(n)')
    print()
    print('  Why? If n = a * b and both a > sqrt(n) and b > sqrt(n), then:')
    print('       a * b > sqrt(n) * sqrt(n) = n')
    print('  This contradicts n = a * b, so one factor must be <= sqrt(n)')
    print()
    print('Example with limit=100 (sqrt=10):')
    print('  We mark multiples of primes [2, 3, 5, 7]')
    print()

    composites = [(91, 7, 13), (77, 7, 11), (51, 3, 17), (39, 3, 13), (87, 3, 29)]
    for n, small, large in composites:
        print(f'  {n} = {small} x {large} -- marked by i={small} (since {small} <= 10)')

    print()


def main():
    parser = argparse.ArgumentParser(
        description='Analyze memory requirements for sieve algorithms'
    )
    parser.add_argument(
        '--verify',
        action='store_true',
        help='Also verify sieve correctness against primesieve'
    )
    parser.add_argument(
        '--explain-sqrt',
        action='store_true',
        help='Explain why sqrt optimization is correct'
    )

    args = parser.parse_args()

    analyze_memory_by_limit()
    analyze_memory_by_n_primes()
    explain_primesieve_optimizations()

    if args.explain_sqrt:
        explain_sqrt_optimization()

    if args.verify:
        verify_sieve_correctness()

    print('Recommendation')
    print('=' * 60)
    print()
    print('Use case                    | Fallback OK? | Recommendation')
    print('-' * 60)
    print('First 100K primes           | Yes (1.7 MB) | Either works')
    print('First 1M primes             | Yes (20 MB)  | Either works')
    print('First 10M primes            | Maybe (234MB)| Prefer primesieve')
    print('All primes up to 1 billion  | No (1 GB)    | Requires primesieve')
    print()


if __name__ == '__main__':
    main()
