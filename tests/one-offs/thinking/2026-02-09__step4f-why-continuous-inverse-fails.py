"""
Step 4F — Why the continuous inverse is fundamentally invalid
=============================================================

Demonstrates with b=7 that you cannot use the continuous
(Sqrt[1+8b]-1)/2 in place of Floor[(Sqrt[1+8b]-1)/2] because:

1. There is no "partial row" in a triangular digit arrangement
2. Digit VALUES change with b (through b - tri(z) + i coefficients),
   not just the number of rows
3. The formula interpolates row count but can't capture coefficient shifts

Date: 2026-02-09
"""

import math


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    """Inverse triangular: largest r such that tri(r) <= b."""
    r = 0
    while tri(r + 1) <= b:
        r += 1
    return r


def stf_direct(b):
    """Direct computation of stf'(b)."""
    r = qg(b)
    return sum(
        sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))
        for z in range(1, r + 1)
    )


# b=7: the triangular arrangement uses digits 0..6 in 3 rows
# Row 1 (z=1): [0]         -> but offset by bt=1, so digit is 1
# Row 2 (z=2): [1,2]       -> digits 2,3
# Row 3 (z=3): [3,4,5]     -> digits 4,5,6
#
# tri(3) = 6, so 6 digits fill 3 rows exactly.
# b=7 means 7 digits -> 3 complete rows with 1 leftover (bt=1)
# The digit VALUES are shifted: each is (b - tri(z) + i) instead of just i

b = 7
r = qg(b)
bt = b - tri(r)
print("b=%d, r=qg(%d)=%d, tri(%d)=%d, bt=%d" % (b, b, r, r, tri(r), bt))
print()
print("Actual rows (discrete, r=%d complete rows):" % r)
total = 0
for z in range(1, r + 1):
    coeffs = [b - tri(z) + i for i in range(z)]
    powers = [b ** (z - 1 - i) for i in range(z)]
    terms = [c * p for c, p in zip(coeffs, powers)]
    row_val = sum(terms)
    total += row_val
    print(
        "  Row %d (z=%d): coeffs=%s, base-7 value = %d" % (z, z, coeffs, row_val)
    )
print("  stf(7) = %d" % total)
print()

# The continuous inverse says r = 3.2749...
r_cont = (math.sqrt(1 + 8 * b) - 1) / 2
print("Continuous inverse: r = (sqrt(%d)-1)/2 = %.6f" % (1 + 8 * b, r_cont))
print("Floor of that:      r = %d" % int(r_cont))
print()
print('What would "row 3.275" mean?')
print("There is no partial row in a triangular digit arrangement.")
print(
    "You either have 3 rows (using %d digits) or 4 rows (using %d digits)."
    % (tri(3), tri(4))
)
print("b=7 has 3 complete rows + 1 leftover digit.")
print()
print("The Mathematica formula effectively interpolates between:")
print(
    "  stf(tri(3)) = stf(6) = %d  (3 exact rows)"
    % sum(
        sum((6 - tri(z) + i) * 6 ** (z - 1 - i) for i in range(z))
        for z in range(1, 4)
    )
)
print(
    "  stf(tri(4)) = stf(10) = %d  (4 exact rows)"
    % sum(
        sum((10 - tri(z) + i) * 10 ** (z - 1 - i) for i in range(z))
        for z in range(1, 5)
    )
)
print("  at r=3.275 it gives: 73.55")
print(
    "  but the actual stf(7) = 105 because the digit VALUES change with b,"
)
print("  not just the number of rows.")
