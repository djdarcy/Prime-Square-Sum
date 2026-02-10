"""
Phase 1 — Verification of sqrt_triangular_discriminant and qg_of_tri
=====================================================================

Verifies:
1. triangular_discriminant_sq: 1 + 8*tri(r) = (2*r+1)^2 for all r
2. sqrt_triangular_discriminant: Nat.sqrt(1+8*tri(r)) = 2*r+1
3. qg_of_tri: qg(tri(r)) = r
4. stf'_closed_form at triangular bases: bt=0 simplification

Date: 2026-02-10
"""

from math import isqrt


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    return (isqrt(1 + 8 * b) - 1) // 2


def stf_direct(b):
    """Direct computation of stf'(b)."""
    r = qg(b)
    return sum(
        sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))
        for z in range(1, r + 1)
    )


# ---- Category 1: Discriminant identity ----
print("=" * 60)
print("Category 1: 1 + 8*tri(r) = (2r+1)^2")
print("=" * 60)

for r in range(0, 51):
    lhs = 1 + 8 * tri(r)
    rhs = (2 * r + 1) ** 2
    assert lhs == rhs, f"FAILED at r={r}: {lhs} != {rhs}"

print(f"  Verified for r = 0..50: all pass")
print()

# ---- Category 2: Nat.sqrt identity ----
print("=" * 60)
print("Category 2: isqrt(1+8*tri(r)) = 2r+1")
print("=" * 60)

for r in range(0, 51):
    assert isqrt(1 + 8 * tri(r)) == 2 * r + 1, f"FAILED at r={r}"

print(f"  Verified for r = 0..50: all pass")
print()

# ---- Category 3: qg_of_tri ----
print("=" * 60)
print("Category 3: qg(tri(r)) = r")
print("=" * 60)

for r in range(0, 51):
    assert qg(tri(r)) == r, f"FAILED at r={r}: qg(tri({r}))={qg(tri(r))}"

print(f"  Verified for r = 0..50: all pass")
print()

# ---- Category 4: stf'_closed_form at b=tri(r), showing bt=0 terms vanish ----
print("=" * 60)
print("Category 4: stf'_closed_form at triangular bases (bt=0)")
print("=" * 60)

for r in range(2, 15):
    b = tri(r)
    bt = b - tri(r)  # = 0
    assert bt == 0, f"bt should be 0 at tri(r)"
    assert qg(b) == r, f"qg(tri({r})) should be {r}"

    stf = stf_direct(b)

    # stf'_closed_form identity with qg(b)=r, bt=0:
    # LHS: 6*(b-1)^4*stf'(b) + 6*r*b*(b-1)^3 + 6*(b-1)^2*tri(r)
    #       + 6*(r+1)*b^(r+1) + 6*b*0*(b-1)^2 + 6*b*(r-1)*(b-1)^2 + 6*b^2*(b-1)
    lhs = (
        6 * (b - 1) ** 4 * stf
        + 6 * r * b * (b - 1) ** 3
        + 6 * (b - 1) ** 2 * tri(r)
        + 6 * (r + 1) * b ** (r + 1)
        + 6 * b * bt * (b - 1) ** 2  # bt=0, this vanishes
        + 6 * b * (r - 1) * (b - 1) ** 2
        + 6 * b ** 2 * (b - 1)
    )

    # RHS: (b-1)^3*r*(r-1)*(r-2) + 6*r*b^(r+2) + 6*b + 6*bt*(b-1)^2*b^(r+1)
    #       + 6*(b-1)*b^(r+1)
    rhs = (
        (b - 1) ** 3 * r * (r - 1) * (r - 2)
        + 6 * r * b ** (r + 2)
        + 6 * b
        + 6 * bt * (b - 1) ** 2 * b ** (r + 1)  # bt=0, this vanishes
        + 6 * (b - 1) * b ** (r + 1)
    )

    assert lhs == rhs, f"Identity FAILED at r={r}, b={b}"

    # Extract stf' value from closed form
    # 6*(b-1)^4*stf = RHS - (other LHS terms)
    other_lhs = (
        6 * r * b * (b - 1) ** 3
        + 6 * (b - 1) ** 2 * tri(r)
        + 6 * (r + 1) * b ** (r + 1)
        + 6 * b * (r - 1) * (b - 1) ** 2
        + 6 * b ** 2 * (b - 1)
    )
    N = rhs - other_lhs
    assert N == 6 * (b - 1) ** 4 * stf
    assert N % (6 * (b - 1) ** 4) == 0
    assert N // (6 * (b - 1) ** 4) == stf

    print(f"  r={r:2d}, b=tri({r})={b:4d}: stf'={stf}, identity verified")

print()

# ---- Category 5: Simplified identity at tri bases (bt=0 terms removed) ----
print("=" * 60)
print("Category 5: Simplified stf'_at_tri identity")
print("=" * 60)
print()
print("At b = tri(r) with bt = 0, the identity simplifies to:")
print()
print("  6*(b-1)^4*stf'(b)")
print("  + 6*r*b*(b-1)^3 + 6*(b-1)^2*tri(r) + 6*(r+1)*b^(r+1)")
print("  + 6*b*(r-1)*(b-1)^2 + 6*b^2*(b-1)")
print("  =")
print("  (b-1)^3*r*(r-1)*(r-2) + 6*r*b^(r+2) + 6*b + 6*(b-1)*b^(r+1)")
print()
print("(Both bt-dependent terms vanish since bt = b - tri(qg(b)) = 0)")
print()
print("All assertions passed.")
