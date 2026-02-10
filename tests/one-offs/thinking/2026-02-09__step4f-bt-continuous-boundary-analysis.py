"""
Step 4F — bt-continuous boundary analysis
==========================================

Follow-up to principled-continuous-extensions.py. Two explorations:

1. The linspace artifact: Category 3 of the previous script showed small
   discrepancies at non-integer bt values. This was a linspace sampling
   artifact — at EXACT integer bt, the Lean formula matches perfectly.

2. Regime boundary discontinuities: F_r(bt=r+1) != F_{r+1}(bt=0).
   The jump at each boundary is EXACTLY rv'(b, r+1) — the value of the
   new row that appears when r increments. The piecewise-analytic form
   is genuinely discontinuous at regime boundaries; the discontinuity
   is the new row's contribution.

Date: 2026-02-09
"""

import numpy as np


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


def rv_prime(b, z):
    """rowValue'(b, z) = Sum_{i<z} (b - tri(z) + i) * b^(z-1-i)."""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def stf_lean_formula(b, r, bt):
    """Lean closed form evaluated at given b, r, bt.
    Works for real-valued b and bt as long as r is integer.
    Returns stf'(b) = (RHS - LHS_extra) / (6*(b-1)^4).
    """
    t = r * (r + 1) / 2  # tri(r), use float division for real bt

    rhs = (
        (b - 1) ** 3 * r * (r - 1) * (r - 2)
        + 6 * r * b ** (r + 2)
        + 6 * b
        + 6 * bt * (b - 1) ** 2 * b ** (r + 1)
        + 6 * (b - 1) * b ** (r + 1)
    )

    lhs_extra = (
        6 * r * b * (b - 1) ** 3
        + 6 * (b - 1) ** 2 * t
        + 6 * (r + 1) * b ** (r + 1)
        + 6 * b * bt * (b - 1) ** 2
        + 6 * b * (r - 1) * (b - 1) ** 2
        + 6 * b ** 2 * (b - 1)
    )

    denom = 6 * (b - 1) ** 4
    if abs(denom) < 1e-15:
        return float("inf")
    return (rhs - lhs_extra) / denom


# ---- Category 1: Exact integer bt values vs linspace artifact ----
# The previous script used np.linspace which didn't hit exact integer bt,
# causing small apparent discrepancies. At EXACT integer bt, the match
# is perfect for bt in [0, r].
print("=" * 70)
print("Category 1: Exact integer bt — Lean formula matches perfectly")
print("  (linspace artifact from previous script explained)")
print("=" * 70)

for r in [3, 4, 5]:
    b_base = tri(r)
    print()
    print("  Regime r=%d (b_base = tri(%d) = %d):" % (r, r, b_base))
    for bt in range(r + 2):
        b = b_base + bt
        lean = stf_lean_formula(b, r, bt)
        direct = stf_direct(b)
        in_regime = bt <= r
        match = abs(lean - direct) < 0.5
        marker = ""
        if not in_regime:
            marker = " <-- bt > r, outside regime (r+1 changes here)"
        elif not match:
            marker = " <-- MISMATCH"
        print(
            "    bt=%d, b=%d: lean=%.1f, direct=%d, match=%s%s"
            % (bt, b, lean, direct, match, marker)
        )

print()
print("  Key: At exact integer bt in [0, r], the Lean formula matches")
print("  perfectly. At bt = r+1, we cross into the next regime and the")
print("  formula (using old r) gives a different value than direct.")

# ---- Category 2: Linspace vs exact comparison for r=5 ----
print()
print("=" * 70)
print("Category 2: Linspace sampling vs exact integer sampling")
print("=" * 70)

r = 5
print()
print("  np.linspace(0, 5.99, 13) gives these bt values:")
for x in np.linspace(0, 5.99, 13):
    print("    bt = %.4f%s" % (x, " <-- not integer!" if abs(x - round(x)) > 0.01 else ""))

print()
print("  The bt=0.9983 is evaluated at b=15.998, NOT b=16.")
print("  stf_lean(15.998, 5, 0.998) = %.4f" % stf_lean_formula(15.998, 5, 0.998))
print("  stf_lean(16, 5, 1) = %.1f" % stf_lean_formula(16, 5, 1))
print("  stf_direct(16) = %d" % stf_direct(16))
print("  The formula is correct — the sampling was just off-grid.")


# ---- Category 3: Boundary discontinuity = new row value ----
# At b = tri(r+1), F_r(bt=r+1) + rv'(b, r+1) = F_{r+1}(bt=0).
# The jump is exactly the value of the new row that opens.
print()
print("=" * 70)
print("Category 3: Regime boundary jump = rv'(b, r+1)")
print("  The discontinuity at each boundary is exactly the new row's value")
print("=" * 70)

print()
print("  %3s %8s %15s %15s %12s %12s %8s"
      % ("r", "b=tri(r+1)", "F_r(bt=r+1)", "F_{r+1}(bt=0)", "jump", "rv'(b,r+1)", "match?"))
print("  " + "-" * 80)

for r in range(2, 9):
    b = tri(r + 1)
    # Left limit: regime r with bt = r+1
    val_left = stf_lean_formula(b, r, r + 1)
    # Right value: regime r+1 with bt = 0
    val_right = stf_lean_formula(b, r + 1, 0)
    # Direct computation for sanity
    direct = stf_direct(b)
    # The new row rv'(b, r+1) at z=r+1
    rv_new = rv_prime(b, r + 1)
    jump = val_right - val_left
    match = abs(jump - rv_new) < 0.5
    print(
        "  %3d %8d %15.0f %15.0f %12.0f %12d %8s"
        % (r, b, val_left, val_right, jump, rv_new, "OK" if match else "FAIL")
    )

print()
print("  Interpretation:")
print("    F_r(bt) smoothly interpolates WITHIN a regime (fixed row count).")
print("    At the boundary b = tri(r+1), a new row (z=r+1) opens up,")
print("    contributing rv'(b, r+1) = Sum_{i<r+1} (b-tri(r+1)+i) * b^(r-i).")
print("    This is a genuine discrete event — you can't have 'half a row'.")
print()
print("    The piecewise-analytic form is:")
print("      stf'(b) = F_r(b - tri(r))  where r = qg(b)")
print("    This is smooth on each interval [tri(r), tri(r+1)) but has")
print("    upward jumps of rv'(b, r+1) at each triangular number b = tri(r+1).")
print()
print("    This is the CORRECT behavior — the Mathematica Sqrt form")
print("    'smooths over' these jumps, which is why it gives wrong values")
print("    between triangular bases.")


# ---- Category 4: The three forms compared ----
print()
print("=" * 70)
print("Category 4: Three continuous forms compared")
print("=" * 70)
print()
print("  | Form                  | Domain              | Boundary behavior     | Use case           |")
print("  |-----------------------|---------------------|-----------------------|--------------------|")
print("  | Discrete (Lean)       | b in N, b >= 2      | Exact at all integers | Computation, proof |")
print("  | bt-continuous (new)   | bt in R, r in N     | Discontinuous at      | Interpolation,     |")
print("  |                       |                     | regime boundaries     | divisibility       |")
print("  |                       |                     | (jump = new row)      |                    |")
print("  | Sqrt-continuous (2010)| b in R, b >= 2      | Smooth everywhere     | Growth rate        |")
print("  |                       |                     | but WRONG between     | envelope only      |")
print("  |                       |                     | triangular bases      |                    |")
print()
print("  The bt-continuous form is the principled 'sqrt(-1) move':")
print("  enlarge bt from N to R (preserving coefficient structure)")
print("  rather than r from N to R (erasing it).")
