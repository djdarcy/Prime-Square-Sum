#!/usr/bin/env python
"""
Sieve Algorithm Benchmark - Comparing all implementations at 100k primes.

Created: 2026-02-04
Related Issues: #7 (GPU sieving), #29 (segmented sieve), #33 (bit-packed)
Context: After v0.7.5 implemented segmented and individual sieves, benchmark all.

Results (on RTX 5090 / AMD system):
- primesieve:    0.64 ms  (3.6x faster than basic)
- basic:         2.32 ms  (baseline)
- segmented:     6.28 ms  (2.7x slower)
- segmented(10k):15.74 ms (6.8x slower)
- individual:  1096.96 ms (473x slower)

Conclusion: primesieve remains optimal for speed. Segmented trades speed for
bounded memory. Individual is only for extreme memory constraints.
"""

import time
import sys
import math

# Add project root to path
sys.path.insert(0, '.')

from utils.sieve import (
    generate_primes, _basic_sieve, _segmented_sieve, _individual_sieve,
    PRIMESIEVE_AVAILABLE, DEFAULT_SEGMENT_SIZE, nth_prime
)


def benchmark_algorithm(name, func, *args, runs=3, **kwargs):
    """Run an algorithm multiple times and return average time."""
    times = []
    result = None
    for _ in range(runs):
        start = time.perf_counter()
        result = func(*args, **kwargs)
        elapsed = time.perf_counter() - start
        times.append(elapsed)
    avg_time = sum(times) / len(times)
    return avg_time, result


def calculate_memory_estimates(limit):
    """Calculate theoretical memory usage for each algorithm."""
    sqrt_limit = int(math.sqrt(limit)) + 1
    small_primes_approx = sqrt_limit / math.log(sqrt_limit)

    return {
        'basic': limit,  # 1 byte per bool
        'segmented_10M': (small_primes_approx * 8) + 10_000_000,
        'segmented_10k': (small_primes_approx * 8) + 10_000,
        'individual': 100_000 * 8,  # Only stores found primes
        'bit_packed': limit / 8,  # Theoretical
    }


def main():
    # Find 100,000th prime for fair comparison
    print('Finding 100,000th prime for fair comparison...')
    upper_limit = nth_prime(100_000)
    print(f'100,000th prime is {upper_limit:,}')
    print(f'Will generate all primes up to {upper_limit:,}')
    print()

    results = {}

    # Test primesieve
    if PRIMESIEVE_AVAILABLE:
        import primesieve
        avg_time, primes = benchmark_algorithm(
            'primesieve',
            primesieve.primes,
            upper_limit
        )
        results['primesieve'] = {'time': avg_time, 'count': len(primes)}
        print(f'primesieve:    {avg_time*1000:8.2f} ms  ({len(primes):,} primes)')
    else:
        print('primesieve:    NOT AVAILABLE')

    # Test basic sieve
    avg_time, primes = benchmark_algorithm('basic', _basic_sieve, upper_limit)
    results['basic'] = {'time': avg_time, 'count': len(primes)}
    print(f'basic:         {avg_time*1000:8.2f} ms  ({len(primes):,} primes)')

    # Test segmented sieve (default segment)
    avg_time, primes = benchmark_algorithm('segmented', _segmented_sieve, upper_limit)
    results['segmented'] = {'time': avg_time, 'count': len(primes)}
    print(f'segmented:     {avg_time*1000:8.2f} ms  ({len(primes):,} primes) [segment={DEFAULT_SEGMENT_SIZE:,}]')

    # Test segmented sieve (small segment)
    small_segment = 10_000
    avg_time, primes = benchmark_algorithm(
        'segmented_small',
        _segmented_sieve,
        upper_limit,
        segment_size=small_segment
    )
    results['segmented_small'] = {'time': avg_time, 'count': len(primes)}
    print(f'segmented(10k):{avg_time*1000:8.2f} ms  ({len(primes):,} primes) [segment={small_segment:,}]')

    # Test individual sieve (much slower)
    print('individual:    Testing... (this takes longer)', end='', flush=True)
    avg_time, primes = benchmark_algorithm('individual', _individual_sieve, upper_limit, runs=1)
    results['individual'] = {'time': avg_time, 'count': len(primes)}
    print(f'\rindividual:    {avg_time*1000:8.2f} ms  ({len(primes):,} primes)')

    # Relative performance
    print()
    print('=' * 60)
    print('RELATIVE PERFORMANCE (vs basic sieve)')
    print('=' * 60)
    base = results['basic']['time']
    for name, data in results.items():
        ratio = data['time'] / base
        if ratio < 1:
            print(f'{name:15s}: {ratio:.2f}x faster')
        else:
            print(f'{name:15s}: {ratio:.2f}x slower')

    # Memory estimates
    print()
    print('=' * 60)
    print('MEMORY USAGE ESTIMATES')
    print('=' * 60)
    mem = calculate_memory_estimates(upper_limit)
    print(f"basic:          {mem['basic'] / 1024 / 1024:.2f} MB")
    print(f"segmented:      {mem['segmented_10M'] / 1024 / 1024:.2f} MB")
    print(f"segmented(10k): {mem['segmented_10k'] / 1024:.2f} KB")
    print(f"individual:     {mem['individual'] / 1024:.2f} KB")
    print(f"bit-packed:     {mem['bit_packed'] / 1024 / 1024:.2f} MB (theoretical)")

    return results


if __name__ == '__main__':
    main()
