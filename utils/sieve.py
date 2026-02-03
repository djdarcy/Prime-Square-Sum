"""
sieve.py - Optimized prime generation using primesieve
========================================================

This module wraps the primesieve library, which is the fastest
known implementation of the Sieve of Eratosthenes (written in C++).

If primesieve is not available, falls back to a pure Python
implementation (much slower but functional).

Usage:
    from utils.sieve import generate_primes, nth_prime

    # Generate all primes up to 1 million
    primes = generate_primes(1_000_000)

    # Get the 1000th prime
    p = nth_prime(1000)  # Returns 7919
"""

import numpy as np
from typing import List, Optional
import warnings
import os

# Try to import primesieve (fast C++ implementation)
try:
    import primesieve
    PRIMESIEVE_AVAILABLE = True
except ImportError:
    PRIMESIEVE_AVAILABLE = False

# Track if we've warned about primesieve (warn once per session)
_primesieve_warned = False


def _warn_no_primesieve():
    """Warn once per session that primesieve is not available."""
    global _primesieve_warned
    if _primesieve_warned or os.environ.get('PRIME_SQUARE_SUM_QUIET'):
        return
    _primesieve_warned = True
    warnings.warn(
        "primesieve not available - using slower Python fallback.\n"
        "  Install: pip install primesieve (Linux/Mac)\n"
        "           conda install -c conda-forge primesieve (Windows)\n"
        "  Silence: set PRIME_SQUARE_SUM_QUIET=1"
    )


def generate_primes(limit: int) -> np.ndarray:
    """
    Generate all primes up to (but not including) limit.

    Args:
        limit: Upper bound (exclusive)

    Returns:
        numpy array of primes

    Example:
        >>> generate_primes(20)
        array([2, 3, 5, 7, 11, 13, 17, 19])
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    if PRIMESIEVE_AVAILABLE:
        primes = primesieve.primes(limit)
        return np.array(primes, dtype=np.int64)
    else:
        _warn_no_primesieve()
        return _python_sieve(limit)


def generate_primes_range(start: int, stop: int) -> np.ndarray:
    """
    Generate all primes in range [start, stop).

    Args:
        start: Lower bound (inclusive)
        stop: Upper bound (exclusive)

    Returns:
        numpy array of primes in range
    """
    if PRIMESIEVE_AVAILABLE:
        primes = primesieve.primes(start, stop)
        return np.array(primes, dtype=np.int64)
    else:
        _warn_no_primesieve()
        # Fallback: generate all up to stop, then filter
        all_primes = _python_sieve(stop)
        return all_primes[all_primes >= start]


def generate_n_primes(n: int) -> np.ndarray:
    """
    Generate the first n primes.

    Args:
        n: Number of primes to generate

    Returns:
        numpy array of first n primes

    Example:
        >>> generate_n_primes(7)
        array([2, 3, 5, 7, 11, 13, 17])
    """
    if n <= 0:
        return np.array([], dtype=np.int64)

    if PRIMESIEVE_AVAILABLE:
        primes = primesieve.n_primes(n)
        return np.array(primes, dtype=np.int64)
    else:
        _warn_no_primesieve()
        # Estimate upper bound using prime number theorem
        # p_n ~ n * (ln(n) + ln(ln(n))) for n > 5
        import math
        if n < 6:
            limit = 15
        else:
            ln_n = math.log(n)
            limit = int(n * (ln_n + math.log(ln_n)) * 1.3)  # 1.3 safety factor

        primes = _python_sieve(limit)
        while len(primes) < n:
            limit = int(limit * 1.5)
            primes = _python_sieve(limit)

        return primes[:n]


def nth_prime(n: int) -> int:
    """
    Return the nth prime (1-indexed).

    Args:
        n: Which prime to return (1 = first prime = 2)

    Returns:
        The nth prime number

    Example:
        >>> nth_prime(7)
        17
        >>> nth_prime(1000)
        7919
    """
    if n <= 0:
        raise ValueError("n must be positive (1-indexed)")

    if PRIMESIEVE_AVAILABLE:
        return primesieve.nth_prime(n)
    else:
        primes = generate_n_primes(n)
        return int(primes[n - 1])


def prime_count(limit: int) -> int:
    """
    Count primes up to limit (prime counting function pi(x)).

    Args:
        limit: Upper bound

    Returns:
        Number of primes <= limit

    Example:
        >>> prime_count(100)
        25
    """
    if PRIMESIEVE_AVAILABLE:
        return primesieve.count_primes(limit)
    else:
        return len(generate_primes(limit + 1))


def _python_sieve(limit: int) -> np.ndarray:
    """
    Pure Python Sieve of Eratosthenes (fallback).

    This is O(n log log n) - correct algorithm but slower than C++.

    Args:
        limit: Upper bound (exclusive)

    Returns:
        numpy array of primes
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    # Boolean array: is_prime[i] = True if i is prime
    is_prime = np.ones(limit, dtype=bool)
    is_prime[0] = is_prime[1] = False

    # Sieve
    for i in range(2, int(limit ** 0.5) + 1):
        if is_prime[i]:
            # Mark multiples of i as composite
            is_prime[i*i::i] = False

    # Extract primes
    return np.nonzero(is_prime)[0].astype(np.int64)


# Quick verification
if __name__ == "__main__":
    print(f"primesieve available: {PRIMESIEVE_AVAILABLE}")
    print()

    # Test basic generation
    primes = generate_primes(100)
    print(f"Primes up to 100: {primes}")
    print(f"Count: {len(primes)}")
    print()

    # Test nth prime
    print(f"7th prime: {nth_prime(7)} (expected: 17)")
    print(f"1000th prime: {nth_prime(1000)} (expected: 7919)")
    print()

    # Test first n primes
    first_7 = generate_n_primes(7)
    print(f"First 7 primes: {first_7}")
    print(f"Sum of squares: {sum(p**2 for p in first_7)} (expected: 666)")
