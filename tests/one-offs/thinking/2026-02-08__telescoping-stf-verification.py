"""
Phase 3D Step 5d: Verify telescoping of stf via the recursive relation.

The proven recursive relation (additive form):
  rowValue'(b, z+1) + (z+1) * G(z+1) = b * rowValue'(b, z) + (b - tri(z) + z)

where G(z+1) = Σ_{i<z+1} b^i = (b^(z+1) - 1)/(b-1)

Summing over z = 0 to r-1 (where r = qg(b)):
  LHS: Σ_{z=0}^{r-1} rowValue'(b, z+1) + Σ_{z=0}^{r-1} (z+1)*G(z+1)
     = stf'(b) + Σ_{z=0}^{r-1} (z+1)*G(z+1)

  RHS: b * Σ_{z=0}^{r-1} rowValue'(b, z) + Σ_{z=0}^{r-1} (b - tri(z) + z)

The RHS first sum: Σ_{z=0}^{r-1} rowValue'(b, z)
  = rowValue'(b, 0) + Σ_{z=1}^{r-1} rowValue'(b, z)
  = 0 + (stf'(b) - rowValue'(b, r))
  = stf'(b) - rowValue'(b, r)

So: stf'(b) + C = b*(stf'(b) - rowValue'(b, r)) + B
where C = Σ (z+1)*G(z+1), B = Σ (b - tri(z) + z)

Rearranging: stf'(b) - b*stf'(b) = -b*rowValue'(b, r) + B - C
  stf'(b)*(1 - b) = -b*rowValue'(b, r) + B - C
  stf'(b)*(b - 1) = b*rowValue'(b, r) - B + C
  stf'(b) = (b*rowValue'(b, r) + C - B) / (b - 1)
"""
import math


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    r = (-1 + int(math.isqrt(1 + 8 * b))) // 2
    if tri(r) == b:
        return r
    return None


def rowValue_prime(b, z):
    """rowValue'(b, z) = Σ_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def geom_sum(b, n):
    """G(n) = Σ_{i<n} b^i = (b^n - 1)/(b-1) for b >= 2"""
    return sum(b ** i for i in range(n))


def stf_prime(b):
    r = qg(b)
    return sum(rowValue_prime(b, z + 1) for z in range(r))


if __name__ == "__main__":
    print("=== Telescoping verification ===\n")

    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 666]:
        r = qg(b)
        if r is None:
            continue

        stf_val = stf_prime(b)

        # Correction sum: C = Σ_{z=0}^{r-1} (z+1) * G(z+1)
        C = sum((z + 1) * geom_sum(b, z + 1) for z in range(r))

        # Boundary sum: B = Σ_{z=0}^{r-1} (b - tri(z) + z)
        B = sum(b - tri(z) + z for z in range(r))

        # rowValue'(b, r) — the last row value
        rv_r = rowValue_prime(b, r)

        # Formula: stf'(b) = (b * rv_r + C - B) / (b - 1)
        numerator = b * rv_r + C - B
        if (b - 1) != 0:
            formula_val = numerator // (b - 1)
            exact = numerator % (b - 1) == 0
        else:
            formula_val = None
            exact = False

        match = formula_val == stf_val
        print(f"b={b:>3} (r={r}): stf={stf_val}, formula={formula_val}, "
              f"exact_div={exact}, match={match}")

        if not match:
            print(f"  DEBUG: b*rv_r={b * rv_r}, C={C}, B={B}, num={numerator}")

    print("\n=== Boundary term analysis ===\n")

    # Check rowValue'(b, 0) = 0 for all bases
    for b in [3, 6, 10, 15, 45]:
        print(f"rowValue'({b}, 0) = {rowValue_prime(b, 0)}")

    print()

    # For triangular bases, check if rowValue'(tri(r), r+1) has a pattern
    print("=== rowValue'(b, r+1) for triangular bases (the 'next row beyond last') ===\n")
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55]:
        r = qg(b)
        rv_next = rowValue_prime(b, r + 1)
        print(f"b={b:>2} (r={r}): rowValue'(b, r+1) = {rv_next}, "
              f"b-tri(r+1) = {b - tri(r + 1)}")

    print("\n=== Correction sum C breakdown ===\n")
    for b in [10]:
        r = qg(b)
        print(f"b={b}, r={r}")
        for z in range(r):
            g = geom_sum(b, z + 1)
            term = (z + 1) * g
            print(f"  z={z}: (z+1)={z + 1}, G(z+1)={g}, term={term}")
        C = sum((z + 1) * geom_sum(b, z + 1) for z in range(r))
        print(f"  C (total) = {C}")

    print("\n=== Boundary sum B breakdown ===\n")
    for b in [10]:
        r = qg(b)
        print(f"b={b}, r={r}")
        for z in range(r):
            term = b - tri(z) + z
            print(f"  z={z}: b-tri({z})+{z} = {b}-{tri(z)}+{z} = {term}")
        B = sum(b - tri(z) + z for z in range(r))
        print(f"  B (total) = {B}")

    print("\n=== Alternative: Can we simplify B? ===\n")
    # B = Σ_{z=0}^{r-1} (b - tri(z) + z) = r*b + Σ_{z=0}^{r-1} (z - tri(z))
    # tri(z) = z*(z+1)/2, so z - tri(z) = z - z(z+1)/2 = z(1 - (z+1)/2) = z(1-z)/2 = -z(z-1)/2
    # So B = r*b - Sum_{z=0}^{r-1} z*(z-1)/2
    # Sum_{z=0}^{r-1} z*(z-1)/2 = (1/2) * Σ z^2 - z = (1/2)((r-1)r(2r-1)/6 - r(r-1)/2)
    #   = (r-1)*r/2 * ((2r-1)/6 - 1/2) = (r-1)*r/2 * (2r-1-3)/6 = (r-1)*r*(2r-4)/12
    #   = (r-1)*r*(r-2)/6

    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 666]:
        r_val = qg(b)
        if r_val is None:
            continue
        B_actual = sum(b - tri(z) + z for z in range(r_val))
        # z - tri(z) = z - z(z+1)/2 = -z(z-1)/2
        sum_ztri = sum(z * (z - 1) // 2 for z in range(r_val))
        B_formula = r_val * b - sum_ztri
        print(f"b={b:>3} (r={r_val}): B_actual={B_actual}, "
              f"r*b - sum_z(z-1)/2 = {B_formula}, match={B_actual == B_formula}")

    print("\n=== Closed form for Sum_{z=0}^{r-1} z*(z-1)/2 ===\n")
    for r_val in range(1, 15):
        actual = sum(z * (z - 1) // 2 for z in range(r_val))
        # This should be (r-1)*r*(r-2)/6 ... let me check
        # Actually: Σ_{z=0}^{r-1} z(z-1)/2 = Σ_{z=2}^{r-1} z(z-1)/2
        # = (1/2) * Σ_{z=0}^{r-1} (z^2 - z)
        # = (1/2) * ((r-1)*r*(2r-1)/6 - (r-1)*r/2)
        # = (r-1)*r/2 * ((2r-1)/6 - 1/2)
        # = (r-1)*r/2 * ((2r-1-3)/6)
        # = (r-1)*r*(r-2)/6
        formula = (r_val - 1) * r_val * (r_val - 2) // 6 if r_val >= 2 else 0
        print(f"r={r_val:>2}: actual={actual}, (r-1)*r*(r-2)/6={formula}, match={actual == formula}")
