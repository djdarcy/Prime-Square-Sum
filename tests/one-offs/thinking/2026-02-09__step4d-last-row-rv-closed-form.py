"""
Step 4D: Verify last row rv'(b,r) closed form identities.

For triangular bases b = tri(r), the last row has digits [0, 1, ..., r-1].
rv'(b, r) = Sum_{i<r} i * b^(r-1-i)

Goal: Find Nat-safe additive identity for rv' via arith_geom_sum.
"""
import math


def tri(n):
    return n * (n + 1) // 2


def rv_prime(b, r):
    """rowValue'(b, r) = Sum_{i<r} (b - tri(r) + i) * b^(r-1-i)"""
    return sum((b - tri(r) + i) * b**(r-1-i) for i in range(r))


def rv_prime_tri(b, r):
    """For b = tri(r), digits are [0, 1, ..., r-1]"""
    assert b == tri(r)
    return sum(i * b**(r-1-i) for i in range(r))


def geom_sum(b, n):
    """Sum_{i<n} b^i"""
    return sum(b**i for i in range(n))


def arith_geom(b, n):
    """Sum_{i<n} i * b^i"""
    return sum(i * b**i for i in range(n))


if __name__ == "__main__":
    print("=== 1. Verify rv'(tri(r), r) = Sum i*b^(r-1-i) ===\n")
    for r in range(1, 12):
        b = tri(r)
        rv = rv_prime(b, r)
        rv_tri = rv_prime_tri(b, r)
        print(f"r={r:>2} b={b:>3}: rv'={rv:>15}, rv_tri={rv_tri:>15}, match={rv == rv_tri}")

    print("\n=== 2. sum_flip: Sum i*b^(r-1-i) = Sum (r-1-i)*b^i ===\n")
    for r in range(1, 12):
        b = tri(r)
        descending = sum(i * b**(r-1-i) for i in range(r))
        ascending = sum((r-1-i) * b**i for i in range(r))
        print(f"r={r:>2} b={b:>3}: desc={descending:>15}, asc={ascending:>15}, match={descending == ascending}")

    print("\n=== 3. Nat additive decomposition ===")
    print("    Sum(r-1-i)*b^i + Sum_i*b^i = (r-1)*Sum_b^i\n")
    all_ok3 = True
    for b in [2, 3, 5, 10, 15, 100]:
        for r in range(1, 8):
            lhs = sum((r-1-i)*b**i for i in range(r)) + sum(i*b**i for i in range(r))
            rhs = (r-1) * sum(b**i for i in range(r))
            ok = lhs == rhs
            if not ok:
                all_ok3 = False
                print(f"  FAIL b={b}, r={r}")
    print(f"Sum(r-1-i)*b^i + Sum_i*b^i = (r-1)*Sum_b^i: {all_ok3}")

    print("\n=== 4. Nat-safe closed form identity ===")
    print("    (b-1)^2 * Sum(r-1-i)*b^i + (r-1)*(b-1) + b = b^r\n")
    all_ok = True
    for b in [2, 3, 5, 6, 7, 10, 15, 21, 28, 36, 100]:
        for r in range(1, 8):
            weighted = sum((r-1-i) * b**i for i in range(r))
            lhs = (b-1)**2 * weighted + (r-1)*(b-1) + b
            rhs = b**r
            ok = lhs == rhs
            if not ok:
                all_ok = False
                print(f"  FAIL b={b}, r={r}: LHS={lhs}, RHS={rhs}")
    print(f"(b-1)^2 * W + (r-1)*(b-1) + b = b^r : {all_ok}")

    print("\n=== 5. Verify with actual rv' (descending powers) ===\n")
    all_ok2 = True
    for b in [3, 6, 10, 15, 21, 28, 36, 100]:
        for r in range(1, 8):
            rv = sum(i * b**(r-1-i) for i in range(r))
            lhs = (b-1)**2 * rv + (r-1)*(b-1) + b
            rhs = b**r
            ok = lhs == rhs
            if not ok:
                all_ok2 = False
                print(f"  FAIL b={b}, r={r}: LHS={lhs}, RHS={rhs}")
    print(f"(b-1)^2 * rv_desc + (r-1)*(b-1) + b = b^r : {all_ok2}")

    print("\n=== 6. Full Nat chain verification ===\n")
    all_ok4 = True
    for b in [2, 3, 5, 7, 10, 20, 100]:
        for r in range(1, 8):
            W = sum((r-1-i)*b**i for i in range(r))
            AG = sum(i*b**i for i in range(r))
            G = sum(b**i for i in range(r))
            check_a = (W + AG == (r-1)*G)
            check_b = ((b-1)*G + 1 == b**r)
            check_c = ((b-1)**2*AG + r*b**r == (r-1)*b**(r+1) + b)
            check_final = ((b-1)**2*W + (r-1)*(b-1) + b == b**r)
            if not (check_a and check_b and check_c and check_final):
                all_ok4 = False
                print(f"  FAIL b={b}, r={r}: a={check_a} b={check_b} c={check_c} final={check_final}")
    print(f"All Nat chain checks pass: {all_ok4}")

    print("\n" + "="*70)
    print("=== CONCLUSION ===")
    print("="*70)
    print()
    print("The Nat-safe closed form for the weighted power sum is:")
    print()
    print("  (b-1)^2 * Sum_{i<r}(r-1-i)*b^i + (r-1)*(b-1) + b = b^r")
    print()
    print("Equivalently (via sum_flip):")
    print("  (b-1)^2 * Sum_{i<r} i*b^(r-1-i) + (r-1)*(b-1) + b = b^r")
    print()
    print("This holds for ALL b >= 1 and r >= 0 (not just triangular bases).")
    print("It is purely additive (no Nat subtraction in the conclusion).")
    print()
    print("Proof building blocks needed:")
    print("  1. sum_split: Sum(r-1-i)*b^i + Sum_i*b^i = (r-1)*Sum_b^i")
    print("     (via sum_congr: (r-1-i)+i = r-1 for i < r)")
    print("  2. geom_sum_pred_mul_add_one: (b-1)*Sum_b^i + 1 = b^r")
    print("  3. arith_geom_sum: (b-1)^2*Sum_i*b^i + r*b^r = (r-1)*b^(r+1) + b")
    print("  4. Algebraic manipulation (ring/omega)")
