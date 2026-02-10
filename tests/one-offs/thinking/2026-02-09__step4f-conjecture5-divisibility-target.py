"""
Step 4F — Conjecture 5 divisibility target verification
=========================================================

Verifies the precise divisibility condition for Conjecture 5:

  From DCF: 6*(b-1)^4 * stf'(b) = N(b, r, bt)
  Conjecture 5: 6 | stf'(b) when r = k^2
  Equivalent to: 36*(b-1)^4 | N (an EXTRA factor of 6 beyond integrality)

This is important because:
  - 6*(b-1)^4 | N is ALREADY guaranteed (stf' is always an integer)
  - Conjecture 5 requires 36*(b-1)^4 | N (additional factor of 6)
  - The proof target is the extra factor, not the integrality factor

Also verifies the counter-examples: for non-square r, 36*(b-1)^4 does
NOT divide N, confirming the conjecture's "if and only if" direction.

Date: 2026-02-09
"""


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    """Inverse triangular: largest r such that tri(r) <= b."""
    r = 0
    while tri(r + 1) <= b:
        r += 1
    return r


def stf_direct(b):
    """Direct computation of stf'(b) for integer b."""
    r = qg(b)
    return sum(
        sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))
        for z in range(1, r + 1)
    )


def N_from_dcf(b, r, bt):
    """RHS - LHS_extra from the DCF identity: 6*(b-1)^4*stf' = N."""
    rhs = (
        (b - 1) ** 3 * r * (r - 1) * (r - 2)
        + 6 * r * b ** (r + 2)
        + 6 * b
        + 6 * bt * (b - 1) ** 2 * b ** (r + 1)
        + 6 * (b - 1) * b ** (r + 1)
    )
    lhs_extra = (
        6 * r * b * (b - 1) ** 3
        + 6 * (b - 1) ** 2 * tri(r)
        + 6 * (r + 1) * b ** (r + 1)
        + 6 * b * bt * (b - 1) ** 2
        + 6 * b * (r - 1) * (b - 1) ** 2
        + 6 * b ** 2 * (b - 1)
    )
    return rhs - lhs_extra


# ---- Category 1: Positive cases (r = k^2) ----
print("=" * 70)
print("Category 1: 6|stf'(b) iff 36*(b-1)^4 | N — positive cases (r=k^2)")
print("=" * 70)
print()

for k in range(2, 7):
    r = k * k
    b = tri(r)
    bt = 0
    stf = stf_direct(b)
    N = N_from_dcf(b, r, bt)
    factor6 = 6 * (b - 1) ** 4
    factor36 = 36 * (b - 1) ** 4

    # Verify basic DCF identity
    assert factor6 * stf == N, f"DCF identity FAILED for k={k}"

    # Verify equivalence: 6|stf' iff 36*(b-1)^4 | N
    div_stf = stf % 6 == 0
    div_N = N % factor36 == 0
    assert div_stf == div_N, f"Equivalence FAILED for k={k}"
    assert div_stf, f"Conjecture 5 FAILED for k={k}"

    print("  k=%d, r=%d, b=tri(%d)=%d:" % (k, r, r, b))
    print("    stf'(b) = %d" % stf)
    print("    stf'(b) / 6 = %d" % (stf // 6))
    print("    36*(b-1)^4 | N: YES")
    print()


# ---- Category 2: Negative cases (r not a perfect square) ----
print("=" * 70)
print("Category 2: Non-square r — 36*(b-1)^4 does NOT divide N")
print("=" * 70)
print()

for r in [3, 5, 6, 7, 8, 10, 11, 12, 13, 14]:
    b = tri(r)
    bt = 0
    stf = stf_direct(b)
    N = N_from_dcf(b, r, bt)
    factor36 = 36 * (b - 1) ** 4

    assert stf % 6 != 0, f"Unexpected: 6|stf' for non-square r={r}"
    assert N % factor36 != 0, f"Unexpected: 36*(b-1)^4|N for non-square r={r}"

    print("  r=%2d, b=%4d: stf'%%6 = %d, N%%36(b-1)^4 != 0" % (r, b, stf % 6))

print()
print("All assertions passed.")
print()
print("Summary:")
print("  DCF gives: 6*(b-1)^4 * stf'(b) = N")
print("  Integrality (always true): 6*(b-1)^4 | N")
print("  Conjecture 5 (r=k^2 only): 36*(b-1)^4 | N")
print("  The proof target is the EXTRA factor of 6 in the numerator.")
