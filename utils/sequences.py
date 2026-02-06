"""
sequences.py - Mathematical sequence generators
================================================

Provides generators for common mathematical sequences used in
expression evaluation.

Usage:
    from utils.sequences import primesum, fibonacci, factorial, catalan

    primesum(7, 2)  # 666 (sum of first 7 primes squared)
    fibonacci(10)    # 55
    factorial(5)     # 120
    catalan(3)       # 5

Note:
    These functions accept integral values. Floats like 7.0 are converted
    to int, but non-integral floats like 7.5 raise ValueError.
    See Issue #20 for numeric type handling discussion.
"""

from math import factorial as math_factorial
from typing import Optional, Any, Union
import numpy as np

from utils.sieve import generate_n_primes, nth_prime as sieve_nth_prime
from utils.types import _ensure_int


def primesum(n: Union[int, float], power: Union[int, float] = 2, *, _cache=None) -> int:
    """
    Sum of first n primes raised to given power.

    primesum(n, p) = Σ(prime_i^p) for i=1 to n

    Args:
        n: Number of primes to sum (must be non-negative integer)
        power: Exponent to raise each prime to (default: 2)
        _cache: Reserved for future cache integration (Issue #19)

    Returns:
        Sum of first n primes each raised to the given power

    Examples:
        >>> primesum(7, 2)
        666  # 2² + 3² + 5² + 7² + 11² + 13² + 17² = 666
        >>> primesum(3, 1)
        10   # 2 + 3 + 5 = 10
        >>> primesum(1, 2)
        4    # 2² = 4
        >>> primesum(0, 2)
        0    # Sum of zero primes

    Note:
        Currently recomputes on each call. Future versions will support
        O(1) lookup via cumulative cache (Issue #19).
    """
    n = _ensure_int(n, "primesum")
    power = _ensure_int(power, "primesum")

    if n < 0:
        raise ValueError(f"primesum() requires non-negative n, got {n}")

    if n == 0:
        return 0

    # Future: use _cache for O(1) lookup when Issue #19 is implemented
    if _cache is not None:
        # Reserved for future cache integration
        # cache.get_cumulative_sum(n, power)
        pass

    # Current implementation: generate and sum
    primes = generate_n_primes(n)
    return sum(int(p) ** power for p in primes)


# Re-export nth_prime from sieve module
# (Already registered in FunctionRegistry, but export for direct import)
nth_prime = sieve_nth_prime


def fibonacci(n: Union[int, float]) -> int:
    """
    Return the nth Fibonacci number.

    Uses 0-indexed convention where F(0)=0, F(1)=1, F(2)=1.
    Alternatively viewed as 1-indexed: F(1)=1, F(2)=1.

    Args:
        n: Index of Fibonacci number (must be non-negative integer)

    Returns:
        The nth Fibonacci number

    Examples:
        >>> fibonacci(0)
        0
        >>> fibonacci(1)
        1
        >>> fibonacci(2)
        1
        >>> fibonacci(10)
        55
        >>> fibonacci(20)
        6765

    Note:
        Python handles arbitrary precision integers, so this works
        for very large n (though computation time increases).
    """
    n = _ensure_int(n, "fibonacci")

    if n < 0:
        raise ValueError(f"fibonacci() requires non-negative n, got {n}")

    if n == 0:
        return 0
    if n <= 2:
        return 1

    a, b = 1, 1
    for _ in range(n - 2):
        a, b = b, a + b
    return b


def factorial(n: Union[int, float]) -> int:
    """
    Calculate n factorial (n!).

    n! = 1 × 2 × 3 × ... × n
    By convention, 0! = 1.

    Args:
        n: Non-negative integer

    Returns:
        n factorial

    Examples:
        >>> factorial(0)
        1
        >>> factorial(1)
        1
        >>> factorial(5)
        120  # 1 × 2 × 3 × 4 × 5
        >>> factorial(10)
        3628800

    Note:
        Uses math.factorial internally, which is optimized in C.
    """
    n = _ensure_int(n, "factorial")

    if n < 0:
        raise ValueError(f"factorial() requires non-negative n, got {n}")

    return math_factorial(n)


def catalan(n: Union[int, float]) -> int:
    """
    Calculate the nth Catalan number.

    C(n) = (2n)! / ((n+1)! × n!)

    Catalan numbers appear in many combinatorial structures:
    - Number of valid parenthesis combinations
    - Number of binary search trees with n nodes
    - Number of paths in a grid that don't cross the diagonal

    Args:
        n: Non-negative integer index

    Returns:
        The nth Catalan number

    Examples:
        >>> catalan(0)
        1
        >>> catalan(1)
        1
        >>> catalan(2)
        2
        >>> catalan(3)
        5
        >>> catalan(4)
        14
        >>> catalan(5)
        42

    Sequence: 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, ...
    (OEIS A000108)
    """
    n = _ensure_int(n, "catalan")

    if n < 0:
        raise ValueError(f"catalan() requires non-negative n, got {n}")

    # C(n) = (2n)! / ((n+1)! × n!)
    return math_factorial(2 * n) // (math_factorial(n + 1) * math_factorial(n))


# Quick verification when run directly
if __name__ == "__main__":
    print("Sequence generators verification")
    print("=" * 50)
    print()

    print("primesum:")
    print(f"  primesum(7, 2) = {primesum(7, 2)} (expected: 666)")
    print(f"  primesum(3, 1) = {primesum(3, 1)} (expected: 10)")
    print(f"  primesum(0, 2) = {primesum(0, 2)} (expected: 0)")
    print()

    print("fibonacci:")
    print(f"  fibonacci(0) = {fibonacci(0)} (expected: 0)")
    print(f"  fibonacci(1) = {fibonacci(1)} (expected: 1)")
    print(f"  fibonacci(10) = {fibonacci(10)} (expected: 55)")
    print(f"  fibonacci(20) = {fibonacci(20)} (expected: 6765)")
    print()

    print("factorial:")
    print(f"  factorial(0) = {factorial(0)} (expected: 1)")
    print(f"  factorial(5) = {factorial(5)} (expected: 120)")
    print(f"  factorial(10) = {factorial(10)} (expected: 3628800)")
    print()

    print("catalan:")
    print(f"  catalan(0) = {catalan(0)} (expected: 1)")
    print(f"  catalan(3) = {catalan(3)} (expected: 5)")
    print(f"  catalan(5) = {catalan(5)} (expected: 42)")
    print()

    print("nth_prime (re-exported from sieve):")
    print(f"  nth_prime(1) = {nth_prime(1)} (expected: 2)")
    print(f"  nth_prime(7) = {nth_prime(7)} (expected: 17)")
