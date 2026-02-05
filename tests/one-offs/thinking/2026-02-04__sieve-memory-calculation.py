#!/usr/bin/env python
"""
Memory usage calculations for different sieve algorithms.

Created: 2026-02-04
Related Issues: #29 (segmented sieve), #33 (bit-packed sieve)
Context: Document memory/speed tradeoffs for Issue #7 update.

This script calculates theoretical memory usage without running the algorithms.
"""

import sys
import math

sys.path.insert(0, '.')


def calculate_memory(limit):
    """Calculate memory usage for each sieve algorithm."""
    sqrt_limit = int(math.sqrt(limit)) + 1
    # Prime counting approximation: pi(n) ~ n / ln(n)
    small_primes_approx = sqrt_limit / math.log(sqrt_limit) if sqrt_limit > 1 else 0

    return {
        'basic': {
            'bytes': limit,
            'desc': f'boolean array of {limit:,}'
        },
        'segmented_default': {
            'bytes': (small_primes_approx * 8) + 10_000_000,
            'desc': f'sqrt primes (~{int(small_primes_approx):,}) + 10M segment'
        },
        'segmented_10k': {
            'bytes': (small_primes_approx * 8) + 10_000,
            'desc': f'sqrt primes (~{int(small_primes_approx):,}) + 10k segment'
        },
        'individual': {
            'bytes': limit / math.log(limit) * 8 if limit > 1 else 0,
            'desc': f'only stores ~{int(limit / math.log(limit)):,} result primes'
        },
        'bit_packed': {
            'bytes': limit / 8,
            'desc': 'theoretical 8x savings over basic'
        }
    }


def format_bytes(n):
    """Format bytes as human-readable string."""
    if n >= 1024 * 1024 * 1024:
        return f'{n / 1024 / 1024 / 1024:.2f} GB'
    elif n >= 1024 * 1024:
        return f'{n / 1024 / 1024:.2f} MB'
    elif n >= 1024:
        return f'{n / 1024:.2f} KB'
    else:
        return f'{n:.0f} bytes'


def main():
    # Test different limits
    limits = [
        100_000,        # 100k
        1_299_709,      # 100k primes
        10_000_000,     # 10M
        100_000_000,    # 100M
        1_000_000_000,  # 1B
        10_000_000_000, # 10B
    ]

    print('MEMORY USAGE BY LIMIT')
    print('=' * 80)

    for limit in limits:
        print(f'\nLimit: {limit:,}')
        print('-' * 40)
        mem = calculate_memory(limit)
        for algo, data in mem.items():
            print(f'  {algo:20s}: {format_bytes(data["bytes"]):>10s}  ({data["desc"]})')


if __name__ == '__main__':
    main()
