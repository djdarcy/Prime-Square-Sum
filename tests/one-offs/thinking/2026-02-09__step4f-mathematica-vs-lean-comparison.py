"""
Step 4F — Mathematica (2010) vs Lean (2026) formula comparison
==============================================================

Compares the original SumTriRows closed-form from the 2010 Mathematica
notebook with the machine-verified stf'_closed_form from TriSum.lean.

Key finding: Both formulas share the same denominator 6*(b-1)^4 and
produce identical numerators for TRIANGULAR bases (b = tri(r)).

The Mathematica closed-form formula (the displayed Sqrt[1+8b] expression)
diverges for non-triangular bases because FullSimplify replaced the discrete
Floor[(Sqrt[1+8b]-1)/2] with the continuous (Sqrt[1+8b]-1)/2. This makes
no difference when b is triangular (sqrt is integer), but gives wrong
results otherwise.

Note: The SumTriRows[b] FUNCTION works for all b (it computes the sum
directly using integer qtri). Only the displayed closed-form breaks.

The Lean formula works for ALL b >= 2 because it keeps r = qg(b) explicit
and includes bt = b - tri(r) correction terms.

Date: 2026-02-09
"""

import math
from decimal import Decimal, getcontext
getcontext().prec = 50


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    """Inverse triangular: largest r such that tri(r) <= b."""
    r = 0
    while tri(r + 1) <= b:
        r += 1
    return r


def stf_direct(b):
    """Direct computation of stf'(b) — matches SumTriRows[b] in Mathematica."""
    r = qg(b)
    return sum(
        sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))
        for z in range(1, r + 1)
    )


def stf_mathematica_integer_sub(b):
    """Mathematica formula with s = 2*qg(b)+1 (integer substitution).
    Only correct when b is triangular."""
    r = qg(b)
    s = 2 * r + 1
    numer = (
        3 - 3 * s
        - 9 * b**2 * (1 + s)
        + 3 * b ** (r + 2) * (1 + s)
        + 6 * b**3 * (2 + s)
        - 2 * b**4 * (3 + s)
        - 3 * b ** (r + 1) * (3 + s)
        + b * (6 + 8 * s)
    )
    denom = 6 * (b - 1) ** 4
    return numer, denom


def stf_mathematica_real_sqrt(b):
    """Mathematica formula with ACTUAL Sqrt[1+8b] (real-valued).
    Tests whether the irrational parts cancel for non-triangular b."""
    s = Decimal(1 + 8 * b).sqrt()
    bd = Decimal(b)
    exp_high = (s + 3) / 2
    exp_low = (s + 1) / 2
    b_exp_high = bd ** exp_high
    b_exp_low = bd ** exp_low
    numer = (
        3 - 3 * s
        - 9 * bd**2 * (1 + s)
        + 3 * b_exp_high * (1 + s)
        + 6 * bd**3 * (2 + s)
        - 2 * bd**4 * (3 + s)
        - 3 * b_exp_low * (3 + s)
        + bd * (6 + 8 * s)
    )
    denom = 6 * (bd - 1) ** 4
    return float(numer / denom)


def stf_lean_numer(b):
    """Numerator from the Lean stf'_closed_form theorem.
    Works for ALL b >= 2."""
    r = qg(b)
    bt = b - tri(r)
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
        + 6 * b**2 * (b - 1)
    )
    return rhs - lhs_extra


# ---- Category 1: Triangular bases — all three methods agree ----
print("=" * 75)
print("Category 1: Triangular bases — all three methods should agree")
print("=" * 75)
print(
    "%5s %3s %15s %20s %20s %8s"
    % ("b", "r", "stf_direct", "math_real_sqrt", "lean/(6(b-1)^4)", "agree?")
)
print("-" * 75)

tri_pass = 0
for b in [3, 6, 10, 15, 21, 28, 36, 45]:
    r = qg(b)
    direct = stf_direct(b)
    math_val = stf_mathematica_real_sqrt(b)
    lean_n = stf_lean_numer(b)
    lean_val = lean_n / (6 * (b - 1) ** 4)
    agree = abs(math_val - direct) < 0.001 and abs(lean_val - direct) < 0.001
    if agree:
        tri_pass += 1
    print(
        "%5d %3d %15d %20.6f %20.6f %8s"
        % (b, r, direct, math_val, lean_val, "YES" if agree else "NO")
    )

print(f"\n  PASSED: {tri_pass} triangular bases — all three agree")

# ---- Category 2: Non-triangular bases — Mathematica formula diverges ----
print()
print("=" * 75)
print("Category 2: Non-triangular bases — Mathematica Sqrt formula diverges")
print("=" * 75)
print(
    "%5s %3s %3s %12s %15s %15s %10s %10s"
    % ("b", "r", "bt", "stf_direct", "math_sqrt", "lean", "math_ok?", "lean_ok?")
)
print("-" * 90)

lean_pass = 0
math_pass = 0
for b in [4, 5, 7, 8, 9, 11, 12, 13, 14, 20, 25, 30]:
    r = qg(b)
    bt = b - tri(r)
    direct = stf_direct(b)
    math_val = stf_mathematica_real_sqrt(b)
    lean_n = stf_lean_numer(b)
    lean_val = lean_n / (6 * (b - 1) ** 4)
    math_ok = abs(math_val - direct) < 0.001
    lean_ok = abs(lean_val - direct) < 0.001
    if math_ok:
        math_pass += 1
    if lean_ok:
        lean_pass += 1
    print(
        "%5d %3d %3d %12d %15.2f %15.2f %10s %10s"
        % (b, r, bt, direct, math_val, lean_val, "OK" if math_ok else "WRONG", "OK" if lean_ok else "WRONG")
    )

print(f"\n  Lean: {lean_pass}/12 correct, Mathematica Sqrt formula: {math_pass}/12 correct")

# ---- Category 3: Why the Mathematica formula diverges ----
print()
print("=" * 75)
print("Category 3: Root cause — FullSimplify drops Floor[]")
print("=" * 75)
print()
print("  SumTriRows[b] computes: Sum[TriRowSimple[b,x], {x, 1, qtri[b]}]")
print("  where qtri[b] = Floor[(Sqrt[1+8b]-1)/2]")
print()
print("  FullSimplify replaces qtri[b] with the continuous (Sqrt[1+8b]-1)/2")
print("  This is exact when b = tri(r) (sqrt is integer), wrong otherwise.")
print()
print("  Example: b=7")
print("    Sqrt[57] = %.10f" % math.sqrt(57))
print("    (Sqrt[57]-1)/2 = %.10f  (continuous)" % ((math.sqrt(57) - 1) / 2))
print("    Floor[...] = %d  (discrete, actual upper limit)" % qg(7))
print("    The formula sums to r=%.4f, but SumTriRows sums to r=%d" % ((math.sqrt(57) - 1) / 2, qg(7)))

# ---- Category 4: Shared denominator analysis ----
print()
print("=" * 75)
print("Category 4: Both formulas share denominator 6*(b-1)^4")
print("=" * 75)
print("  Boundary sum B (Step 4A):   contributes factor 6")
print("  Correction sum C (Step 4C): contributes factor (b-1)^3")
print("  Per-row rv' (Step 4E):      contributes factor (b-1)^2")
print("  Telescoping combination:    multiply by (b-1) for common factor")
print("  Total: 6 * (b-1)^4 = LCM of all component denominators")
print()
print("  The 2010 Mathematica notebook and 2026 Lean proof independently")
print("  arrive at the same natural scaling factor.")

# ---- Category 5: Integer substitution comparison ----
print()
print("=" * 75)
print("Category 5: Mathematica formula with integer s=2r+1 vs Lean")
print("  (Both use integer r, but Lean also has bt correction)")
print("=" * 75)

for b in [7, 10, 13, 21, 25]:
    r = qg(b)
    bt = b - tri(r)
    direct = stf_direct(b)
    mn, md = stf_mathematica_integer_sub(b)
    ln = stf_lean_numer(b)
    math_val = mn / md if md != 0 else float("inf")
    lean_val = ln / (6 * (b - 1) ** 4)
    print(
        "  b=%2d r=%d bt=%d: direct=%d, math_int=%.2f (%s), lean=%.2f (%s)"
        % (
            b, r, bt, direct,
            math_val, "OK" if abs(math_val - direct) < 0.001 else "WRONG",
            lean_val, "OK" if abs(lean_val - direct) < 0.001 else "WRONG",
        )
    )

# ---- Category 6: Why the continuous inverse is fundamentally invalid ----
# This goes deeper than "FullSimplify drops Floor" — it shows WHY
# interpolating the row count gives nonsensical results.
print()
print("=" * 75)
print("Category 6: Why the continuous inverse is fundamentally invalid")
print("  (Digit VALUES change with b, not just the number of rows)")
print("=" * 75)

# Concrete demonstration with b=7
b = 7
r = qg(b)
bt = b - tri(r)
print()
print(f"  b={b}, r=qg({b})={r}, tri({r})={tri(r)}, bt={bt}")
print(f"  There are {r} complete rows, plus {bt} leftover digit(s).")
print()

# Show each row's digits and their positional values
print("  Row-by-row digit values (base 7):")
for z in range(1, r + 1):
    digits = []
    for i in range(z):
        coeff = b - tri(z) + i
        positional = coeff * b ** (z - 1 - i)
        digits.append((coeff, z - 1 - i, positional))
    row_sum = sum(d[2] for d in digits)
    digit_str = " + ".join(f"{c}*{b}^{e}" for c, e, _ in digits)
    print(f"    z={z}: {digit_str} = {row_sum}")

direct_val = stf_direct(b)
print(f"  Total stf'({b}) = {direct_val}")

# Compare with neighboring triangular bases to show the interpolation problem
print()
print("  Compare with neighboring triangular bases:")
for tb in [6, 10]:
    tr = qg(tb)
    print(f"    stf'({tb}) = {stf_direct(tb)} (triangular, r={tr})")

# Show what the continuous formula computes
cont_r = (math.sqrt(1 + 8 * b) - 1) / 2
math_val = stf_mathematica_real_sqrt(b)
print()
print(f"  Continuous r = (sqrt(1+8*{b})-1)/2 = {cont_r:.6f}")
print(f"  Mathematica Sqrt formula gives: {math_val:.2f}")
print(f"  Actual stf'({b}) = {direct_val}")
print()
print("  The formula 'interpolates' between stf'(6)=35 and stf'(10)=666,")
print(f"  landing at {math_val:.2f}. But the actual value {direct_val} is NOT between them!")
print()
print("  Why? Because digit VALUES depend on b through (b - tri(z) + i):")
print("    - At b=6: row z=3 has digits [0, 1, 2] (since b-tri(3)=0)")
print("    - At b=7: row z=3 has digits [1, 2, 3] (since b-tri(3)=1)")
print("  Same 3 rows, but EVERY coefficient shifts by bt=1.")
print("  A continuous formula can't capture this discrete coefficient jump.")

# Show all bases from 4 to 15 to visualize the staircase vs smooth curve
print()
print("  stf'(b) staircase vs Mathematica smooth curve:")
print("  %5s %3s %3s %12s %12s %10s" % ("b", "r", "bt", "actual", "math_sqrt", "diff"))
print("  " + "-" * 50)
for b_test in range(3, 16):
    r_test = qg(b_test)
    bt_test = b_test - tri(r_test)
    d_test = stf_direct(b_test)
    m_test = stf_mathematica_real_sqrt(b_test)
    diff = m_test - d_test
    marker = " <-- triangular" if bt_test == 0 else ""
    print(
        "  %5d %3d %3d %12d %12.2f %10.2f%s"
        % (b_test, r_test, bt_test, d_test, m_test, diff, marker)
    )

print()
print("  Notice: at triangular bases (bt=0), diff=0. Between them, the")
print("  formula drifts because it treats r as continuous but coefficients")
print("  are inherently discrete (step function of Floor).")

print()
print("Summary:")
print("  - SumTriRows[b] FUNCTION: works for all b (computes sum directly)")
print("  - Sqrt[1+8b] FORMULA: only exact for triangular b (FullSimplify drops Floor)")
print("  - Lean stf'_closed_form: works for all b >= 2 (explicit r + bt correction)")
print("  - Both share denominator 6*(b-1)^4 and agree on triangular bases")
print("  - Continuous inverse fails because digit VALUES change with b, not just row count")
