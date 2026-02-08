"""
Phase 3D Step 5: Verify the ADDITIVE form of the telescoping identity.

We want to prove in Lean (avoiding Nat subtraction underflow):
  stf'(b) + C + b * rowValue'(b, r) = b * stf'(b) + B

where r = qg(b), and:
  C = Sum_{z<r} (z+1) * G(z+1)     (correction sum)
  B = Sum_{z<r} (b - tri(z) + z)    (boundary sum)
  G(n) = Sum_{i<n} b^i              (geometric sum)

Also verify the intermediate lemma (index shift):
  Sum_{z<r} rowValue'(b,z) + rowValue'(b,r) = stf'(b)
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
    """rowValue'(b, z) = Sum_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def geom_sum(b, n):
    """G(n) = Sum_{i<n} b^i"""
    return sum(b ** i for i in range(n))


def stf_prime(b):
    r = qg(b)
    return sum(rowValue_prime(b, z + 1) for z in range(r))


if __name__ == "__main__":
    print("=== Index shift verification ===\n")
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 666]:
        r = qg(b)
        if r is None:
            continue

        stf_val = stf_prime(b)
        sum_rv_z = sum(rowValue_prime(b, z) for z in range(r))
        rv_r = rowValue_prime(b, r)

        shift_ok = (sum_rv_z + rv_r == stf_val)
        print(f"b={b:>3} (r={r}): sum_rv={sum_rv_z}, rv_r={rv_r}, "
              f"sum+rv_r={sum_rv_z + rv_r}, stf={stf_val}, shift_ok={shift_ok}")

    print("\n=== Additive-form telescoping verification ===\n")
    print("Goal: stf'(b) + C + b*rv'(b,r) = b*stf'(b) + B\n")

    all_ok = True
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 666]:
        r = qg(b)
        if r is None:
            continue

        stf_val = stf_prime(b)
        rv_r = rowValue_prime(b, r)

        # C = Sum_{z<r} (z+1) * G(z+1)
        C = sum((z + 1) * geom_sum(b, z + 1) for z in range(r))

        # B = Sum_{z<r} (b - tri(z) + z)
        B = sum(b - tri(z) + z for z in range(r))

        LHS = stf_val + C + b * rv_r
        RHS = b * stf_val + B

        ok = (LHS == RHS)
        if not ok:
            all_ok = False
        print(f"b={b:>3} (r={r}): stf={stf_val}, C={C}, B={B}, rv_r={rv_r}, "
              f"LHS={LHS}, RHS={RHS}, match={ok}")

    print(f"\nAll additive-form checks passed: {all_ok}")

    print("\n=== Also verify the subtraction form (for comparison) ===\n")
    print("stf'(b) + C = b*(stf'(b) - rv'(b,r)) + B\n")
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66]:
        r = qg(b)
        if r is None:
            continue
        stf_val = stf_prime(b)
        rv_r = rowValue_prime(b, r)
        C = sum((z + 1) * geom_sum(b, z + 1) for z in range(r))
        B = sum(b - tri(z) + z for z in range(r))

        LHS = stf_val + C
        RHS = b * (stf_val - rv_r) + B
        print(f"b={b:>3}: LHS={LHS}, RHS={RHS}, match={LHS == RHS}")
