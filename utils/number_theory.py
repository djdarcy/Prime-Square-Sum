"""
number_theory.py - Mathematical utilities for number theory operations
======================================================================

Provides:
- Digital root utilities for primality pre-filtering
- Triangular number functions (tri, qtri, trisum, is_triangular)
- General number theory tools

Usage:
    from utils.number_theory import digital_root, could_be_prime_by_digital_root
    from utils.number_theory import tri, qtri, trisum, is_triangular

    # Quick filter: is 37 potentially prime?
    if could_be_prime_by_digital_root(37):
        # Could be prime, worth testing further
        result = expensive_primality_test(37)

    # Compute digital root
    dr = digital_root(666)  # Returns 9 (definitely divisible by 3)

    # Triangular numbers
    tri(36)        # Returns 666
    qtri(666)      # Returns 36 (inverse)
    trisum(10)     # Returns 666 (row-sum of digit triangle)
"""

from typing import Optional
import math

from utils.types import _ensure_int


def digital_root(n) -> int:
    """
    Calculate digital root (repeated digit sum to single digit).

    The digital root is obtained by repeatedly summing the digits of a number
    until a single digit remains.

    Formula: digitalRoot(n) = 1 + ((n - 1) mod 9) for n > 0

    Args:
        n: Integer or string representation of a number

    Returns:
        Single digit (0-9)

    Examples:
        >>> digital_root(38)
        2  # 3 + 8 = 11, then 1 + 1 = 2

        >>> digital_root(666)
        9  # 6 + 6 + 6 = 18, 1 + 8 = 9, or via formula: 1 + ((666 - 1) % 9) = 9

        >>> digital_root(9)
        9

        >>> digital_root(0)
        0
    """
    if isinstance(n, str):
        n = int(n)

    if n == 0:
        return 0

    return 1 + ((n - 1) % 9)


def could_be_prime(n) -> bool:
    """
    Quick multi-filter primality check combining all trivial pre-filters.

    Eliminates numbers that are *definitely* not prime:
    - Even numbers (except 2)
    - Multiples of 5 (except 5)
    - Multiples of 3 (except 3) via digital root

    Args:
        n: Candidate number

    Returns:
        True if could be prime, False if definitely composite

    Performance: O(1) - much faster than trial division or sieving

    Examples:
        >>> could_be_prime(2)
        True

        >>> could_be_prime(4)  # Even
        False

        >>> could_be_prime(5)
        True

        >>> could_be_prime(15)  # Divisible by 5
        False

        >>> could_be_prime(9)  # Divisible by 3 (digital root = 9)
        False

        >>> could_be_prime(37)
        True
    """
    if n < 2:
        return False

    # Handle small primes
    if n in {2, 3, 5}:
        return True

    # Even numbers (except 2)
    if n % 2 == 0:
        return False

    # Multiples of 5 (except 5)
    if n % 5 == 0:
        return False

    # Multiples of 3 via digital root check (except 3)
    return could_be_prime_by_digital_root(n)


def could_be_prime_by_digital_root(n) -> bool:
    """
    Pre-filter: Quick check for primality based on digital root.

    **Mathematical Result (verified with 1M primes in Mathematica):**

    For primes p > 3: digitalRoot(p) ∉ {0, 3, 6, 9}

    This is because:
    - digitalRoot = 0: Impossible for n > 0
    - digitalRoot = 3: Number is divisible by 3
    - digitalRoot = 6: Number is divisible by 3
    - digitalRoot = 9: Number is divisible by 9 (and thus 3)

    Therefore, primes > 3 can only have digitalRoot ∈ {1, 2, 4, 5, 7, 8}

    **Performance Impact:**
    - Filters out ~40% of odd candidates immediately
    - O(1) computation (much faster than trial division or sieving)
    - Equivalent to checking (n % 3 != 0) for n > 3

    **Use Cases:**
    - Quick spot checks before expensive primality tests
    - Large number filtering when digits are strings (sum >> modulo)
    - Pre-filter before sieving for small candidate sets

    Args:
        n: Candidate number

    Returns:
        True if number could be prime (based on digital root)
        False if number is definitely composite (not prime)

    Examples:
        >>> could_be_prime_by_digital_root(2)
        True  # 2 is prime

        >>> could_be_prime_by_digital_root(3)
        True  # 3 is prime

        >>> could_be_prime_by_digital_root(9)
        False  # 9 = 3^2, digital root = 9 (divisible by 3)

        >>> could_be_prime_by_digital_root(37)
        True  # 37 is prime, digital root = 1

        >>> could_be_prime_by_digital_root(39)
        False  # 39 = 3*13, digital root = 3 (divisible by 3)

        >>> could_be_prime_by_digital_root(666)
        False  # digital root = 9 (divisible by 3)

    Note:
        This is a *necessary but not sufficient* condition for primality.
        Numbers like 25 (5²) pass this filter but are not prime.
        Only use as a pre-filter, not as a definitive primality test.
    """
    if n < 2:
        return False

    if n <= 3:
        return True  # 2 and 3 are prime

    dr = digital_root(n)
    return dr not in {0, 3, 6, 9}


def digital_root_statistics(limit: int) -> dict:
    """
    Analyze digital root distribution in a range of numbers.

    Useful for understanding how effective the digital root filter is
    for a specific range of candidates.

    Args:
        limit: Analyze numbers from 2 to limit

    Returns:
        Dictionary with statistics:
        - total_candidates: Count of numbers 2..limit
        - passes_filter: Count passing digital root filter
        - rejected: Count with digital root in {0, 3, 6, 9}
        - filter_effectiveness: Percentage rejected
    """
    total = limit - 2
    passes = sum(1 for n in range(2, limit) if could_be_prime_by_digital_root(n))
    rejected = total - passes

    return {
        'total_candidates': total,
        'passes_filter': passes,
        'rejected': rejected,
        'filter_effectiveness_percent': round(100 * rejected / total, 1) if total > 0 else 0
    }


def explain_digital_root_filter():
    """Print educational explanation of digital root pre-filtering."""
    print("\nDigital Root Pre-Filtering for Prime Candidates")
    print("=" * 60)
    print()
    print("Mathematical Result (verified with 1M primes in Mathematica):")
    print("  For primes p > 3: digitalRoot(p) ∉ {0, 3, 6, 9}")
    print()
    print("Valid digital roots for primes > 3: {1, 2, 4, 5, 7, 8}")
    print()
    print("This filters out ~40% of candidates (multiples of 3)")
    print()
    print("Examples:")
    print("  37 (prime):     digitalRoot = 1 ✓ Could be prime")
    print("  39 (composite): digitalRoot = 3 ✗ Definitely divisible by 3")
    print("  25 (composite): digitalRoot = 7 ✓ Passes filter (but not prime)")
    print()
    print("Note: Equivalent to checking (n % 3 != 0) but useful for:")
    print("  - String-based operations on huge numbers")
    print("  - Educational demonstration")
    print("  - Manual verification")
    print()


# =============================================================================
# Triangular Number Functions (Issue #14)
# =============================================================================

def tri(n: int) -> int:
    """
    Calculate the nth triangular number.

    The nth triangular number is the sum of integers from 1 to n.
    Formula: T(n) = n(n+1)/2 = (n² + n) / 2

    Args:
        n: Non-negative integer index (accepts integral floats like 36.0)

    Returns:
        The nth triangular number

    Raises:
        ValueError: If n is negative or non-integral float
        TypeError: If n is not a numeric type

    Examples:
        >>> tri(0)
        0
        >>> tri(1)
        1
        >>> tri(4)
        10  # 1 + 2 + 3 + 4 = 10
        >>> tri(36)
        666  # Key relationship from Zero_AG paper
        >>> tri(36.0)
        666  # Integral floats accepted
        >>> tri(36.5)
        ValueError: tri() requires integral value, got 36.5

    Mathematical context:
        - tri(4) = 10 represents all digits in base-10 (0-9)
        - tri(36) = 666, connecting to many mystical number patterns
        - The entire positive number line can be viewed as tri(∞)
    """
    n = _ensure_int(n, "tri")
    if n < 0:
        raise ValueError(f"tri() requires non-negative n, got {n}")
    return (n * n + n) // 2


def qtri(x: int) -> Optional[int]:
    """
    Inverse triangular function. Returns n if x is triangular, None otherwise.

    Solves the quadratic equation n² + n - 2x = 0 for integer n.
    Using quadratic formula: n = (-1 + √(1 + 8x)) / 2

    Args:
        x: Value to test (accepts integral floats like 666.0)

    Returns:
        n such that tri(n) = x, or None if x is not triangular

    Raises:
        ValueError: If x is a non-integral float
        TypeError: If x is not a numeric type

    Examples:
        >>> qtri(0)
        0  # tri(0) = 0
        >>> qtri(1)
        1  # tri(1) = 1
        >>> qtri(10)
        4  # tri(4) = 10
        >>> qtri(666)
        36  # tri(36) = 666
        >>> qtri(666.0)
        36  # Integral floats accepted
        >>> qtri(5)
        None  # 5 is not a triangular number
        >>> qtri(7)
        None  # 7 is not a triangular number
        >>> qtri(666.5)
        ValueError: qtri() requires integral value, got 666.5

    Note:
        This is an O(1) operation using the closed-form inverse formula.
    """
    x = _ensure_int(x, "qtri")
    if x < 0:
        return None
    if x == 0:
        return 0

    # Discriminant: 1 + 8x
    discriminant = 1 + 8 * x

    # Check if discriminant is a perfect square
    sqrt_disc = int(math.isqrt(discriminant))
    if sqrt_disc * sqrt_disc != discriminant:
        return None

    # n = (-1 + sqrt(1 + 8x)) / 2
    # For this to be an integer, (sqrt_disc - 1) must be even
    if (sqrt_disc - 1) % 2 != 0:
        return None

    n = (sqrt_disc - 1) // 2

    # Verify the result (guards against floating-point edge cases)
    if tri(n) == x:
        return n
    return None


def is_triangular(x: int) -> bool:
    """
    Check if x is a triangular number.

    A triangular number is one that can be arranged in an equilateral triangle.
    Sequence: 0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, ...

    Args:
        x: Value to check (accepts integral floats like 666.0)

    Returns:
        True if x is triangular, False otherwise

    Raises:
        ValueError: If x is a non-integral float
        TypeError: If x is not a numeric type

    Examples:
        >>> is_triangular(0)
        True
        >>> is_triangular(1)
        True
        >>> is_triangular(3)
        True
        >>> is_triangular(10)
        True
        >>> is_triangular(666)
        True  # tri(36) = 666
        >>> is_triangular(666.0)
        True  # Integral floats accepted
        >>> is_triangular(5)
        False
        >>> is_triangular(667)
        False
        >>> is_triangular(666.5)
        ValueError: qtri() requires integral value, got 666.5
    """
    return qtri(x) is not None


def trisum(b: int) -> int:
    """
    Calculate the row-sum of a triangular digit arrangement for base b.

    When digits 0 through (b-1) are arranged in a triangular pattern
    and summed row by row, this function returns the total.

    For base 10 (digits 0-9):
            9       = 9
           78       = 78
          456       = 456
         0123       = 123
        ------
        Total: 123 + 456 + 78 + 9 = 666

    The formula derives from the Zero_AG/Scarcity Framework paper.

    Args:
        b: Base (number of digits = b, from 0 to b-1)
           Accepts integral floats like 10.0

    Returns:
        The sum of row values in the triangular digit arrangement

    Raises:
        ValueError: If b < 1 or non-integral float
        TypeError: If b is not a numeric type

    Examples:
        >>> trisum(10)
        666  # 0123 + 456 + 78 + 9 = 666
        >>> trisum(10.0)
        666  # Integral floats accepted
        >>> trisum(1)
        0  # Only digit 0
        >>> trisum(2)
        1  # Digits 0,1 arranged as: 1 / 0 = 1 + 0 = 1
        >>> trisum(10.5)
        ValueError: trisum() requires integral value, got 10.5

    Mathematical context:
        This function connects triangular arrangements to the mystical
        significance of 666 in base-10 representation.
    """
    b = _ensure_int(b, "trisum")
    if b < 1:
        raise ValueError(f"trisum() requires b >= 1, got {b}")
    if b == 1:
        return 0  # Only digit 0

    # Find how many complete rows we can form with b digits
    # Row k (1-indexed from bottom) has k digits
    # Total digits in rows 1..r = tri(r)
    # We need tri(r) <= b

    # Find the number of complete rows
    r = qtri(b - 1)  # b-1 because we have digits 0 to b-1
    if r is None:
        # b-1 is not triangular, find largest r where tri(r) <= b-1
        r = 0
        while tri(r + 1) <= b - 1:
            r += 1

    # Build the triangular arrangement
    # Digits fill from bottom-left, going right, then up
    # Bottom row (row 1) has 1 digit, row 2 has 2 digits, etc.
    # But the pattern shows bottom row is longest...

    # Re-reading the example:
    #     9       (row 4, 1 digit: 9)
    #    78       (row 3, 2 digits: 7,8)
    #   456       (row 2, 3 digits: 4,5,6)
    #  0123       (row 1, 4 digits: 0,1,2,3)
    #
    # So row 1 (bottom) has the most digits, row r (top) has 1 digit
    # For b=10 digits (0-9), we have r=4 rows
    # Row k has (r - k + 1) digits... no wait
    # Row 1: 4 digits, Row 2: 3 digits, Row 3: 2 digits, Row 4: 1 digit
    # So row k has (r - k + 1) digits from bottom up

    # Total digits used = 4 + 3 + 2 + 1 = 10 = tri(4)
    # So r = qtri(b) when b is triangular

    # Actually let's compute directly:
    # Find r such that tri(r) = b (if b is triangular) or tri(r) < b < tri(r+1)

    # For b = 10: tri(4) = 10, so r = 4

    # Simpler approach: compute directly
    total = 0
    digit = 0  # Current digit to place (0, 1, 2, ...)

    # Find number of rows
    num_rows = 1
    while tri(num_rows) < b:
        num_rows += 1
    if tri(num_rows) > b:
        num_rows -= 1

    # Now num_rows is such that tri(num_rows) <= b
    # But we may have extra digits that don't fit

    # For exact triangular numbers, tri(num_rows) = b
    digits_used = 0
    row_values = []

    for row in range(num_rows, 0, -1):
        # Row 'row' has 'row' digits when counting from top
        # But in our arrangement, bottom has most digits
        # Row index from bottom: num_rows - row + 1 (has that many spaces)
        # Actually, let me re-think...

        # Looking at example again:
        # Row 1 (bottom): 0123 - 4 digits, forms number 0123 = 123
        # Row 2: 456 - 3 digits, forms number 456
        # Row 3: 78 - 2 digits, forms number 78
        # Row 4 (top): 9 - 1 digit, forms number 9

        # So row k from bottom has (num_rows - k + 1) digits
        pass

    # Let me implement this more directly
    # Digits 0 to b-1 arranged bottom to top, left to right
    # Row sizes from bottom: num_rows, num_rows-1, ..., 2, 1

    digits = list(range(b))  # [0, 1, 2, ..., b-1]
    idx = 0
    total = 0

    for row_size in range(num_rows, 0, -1):
        if idx >= len(digits):
            break
        # Take row_size digits
        row_digits = digits[idx:idx + row_size]
        if len(row_digits) < row_size:
            # Partial row - include if any digits
            if row_digits:
                row_value = int(''.join(map(str, row_digits)))
                total += row_value
            break
        idx += row_size
        # Form number from these digits
        row_value = int(''.join(map(str, row_digits)))
        total += row_value

    return total
