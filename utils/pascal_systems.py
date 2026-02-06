"""
Pascal-Weighted Analytical Tools
================================

Lightweight decomposition and analysis utilities using Pascal's triangle
(binomial coefficients) and figurate number weights.

These are analytical tools — not a formal number system. They provide
decomposition functions useful for investigating stf() structure,
particularly the stf-k² conjecture (6 | stf(tri(k²))).

Origin: 2026-02-06 Pascal-weighted number system exploration.
The "pure center" observation in Row 4 representations led to
discovering the stf-k² divisibility conjecture.
"""

from math import comb, isqrt


def pascal_row_weights(n):
    """Return the binomial coefficients C(n, k) for k = 0..n.

    These are the weights of Pascal's triangle row n.

    Examples:
        >>> pascal_row_weights(0)
        [1]
        >>> pascal_row_weights(4)
        [1, 4, 6, 4, 1]
    """
    return [comb(n, k) for k in range(n + 1)]


def figurate_weights(degree, count):
    """Return figurate number weights along a Pascal diagonal.

    degree=1: natural numbers [1, 2, 3, 4, ...]
    degree=2: triangular numbers [1, 3, 6, 10, ...]
    degree=3: tetrahedral numbers [1, 4, 10, 20, ...]

    Args:
        degree: Which Pascal diagonal (1=natural, 2=triangular, 3=tetrahedral)
        count: How many weights to generate

    Examples:
        >>> figurate_weights(2, 5)
        [1, 3, 6, 10, 15]
    """
    return [comb(degree + i - 1, degree) for i in range(1, count + 1)]


def greedy_canonical(x, weights):
    """Decompose x using weights in greedy (largest-first) order.

    Returns a list of coefficients [c_0, c_1, ..., c_{n-1}] such that
    x = sum(c_i * weights[i]). Uses greedy algorithm: processes weights
    from largest value to smallest, regardless of position.

    Args:
        x: The number to decompose
        weights: List of positional weights (e.g., from pascal_row_weights)

    Returns:
        List of coefficients, same length as weights.

    Examples:
        >>> greedy_canonical(666, pascal_row_weights(4))
        [0, 0, 111, 0, 0]
        >>> greedy_canonical(10, [1, 3, 3, 1])
        [0, 3, 0, 1]
    """
    n = len(weights)
    coeffs = [0] * n
    remaining = x

    # Process by weight value (largest first), not by index
    for i in sorted(range(n), key=lambda j: weights[j], reverse=True):
        if weights[i] > 0 and remaining >= weights[i]:
            coeffs[i] = remaining // weights[i]
            remaining -= coeffs[i] * weights[i]

    return coeffs


def is_pure_center(coeffs):
    """Check if a decomposition has the "pure center" form.

    A pure center representation has nonzero values only at the
    center position(s). For odd-length coefficient lists, this means
    only the middle element is nonzero.

    This pattern is significant because it indicates divisibility by
    the central binomial coefficient (e.g., C(4,2) = 6 for Row 4).

    Args:
        coeffs: List of coefficients from greedy_canonical()

    Returns:
        True if only the center position(s) are nonzero.

    Examples:
        >>> is_pure_center([0, 0, 111, 0, 0])
        True
        >>> is_pure_center([0, 3, 0, 1])
        False
    """
    n = len(coeffs)
    if n == 0:
        return False

    center = n // 2
    for i, c in enumerate(coeffs):
        if i == center and c == 0:
            return False
        if i != center and c != 0:
            return False
    return True


def stf_k_squared_check(k):
    """Check the stf-k² conjecture for a given k value.

    Computes stf(tri(k²)) and checks divisibility by 6.
    Requires computing stf(), which involves summing triangular
    row values — this can be slow for large k.

    Args:
        k: Integer ≥ 2

    Returns:
        Dict with keys: k, r, b, stf_value, div_by_6, stf_div_6,
        row4_repr, is_pure_center
    """
    r = k * k
    b = r * (r + 1) // 2

    # Compute stf(b) using the digit-triangle method
    # Digits 0..b-1 fill bottom-up: bottom row (length r) gets 0..r-1,
    # next row (length r-1) gets r..2r-2, etc. Top row (length 1) gets
    # the last digit. Each row is read as a base-b number.
    digits = list(range(b))
    stf_val = 0
    pos = 0
    for z in range(r, 0, -1):  # bottom row (r digits) to top row (1 digit)
        row_digits = digits[pos:pos + z]
        row_val = 0
        for d in row_digits:
            row_val = row_val * b + d
        stf_val += row_val
        pos += z

    div6 = stf_val % 6 == 0
    row4 = greedy_canonical(stf_val, pascal_row_weights(4))

    return {
        'k': k,
        'r': r,
        'b': b,
        'stf_value': stf_val,
        'div_by_6': div6,
        'stf_div_6': stf_val // 6 if div6 else None,
        'row4_repr': row4,
        'is_pure_center': is_pure_center(row4),
    }
