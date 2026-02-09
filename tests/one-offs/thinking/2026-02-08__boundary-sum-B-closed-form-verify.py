"""
Step 4A: Verify the boundary sum B closed form.

B = Σ_{z<r} (b - tri(z) + z)

Nat-safe additive identity (no division, no subtraction in conclusion):
  6 * B + r*(r-1)*(r-2) = 6*r*b

Decomposition:
  B = r*b + r(r-1)/2 - (r-1)*r*(r+1)/6
  6*B = 6*r*b + 3*r*(r-1) - (r-1)*r*(r+1)
      = 6*r*b - r*(r-1)*(r+1 - 3)
      = 6*r*b - r*(r-1)*(r-2)

Induction step verification:
  Adding term at z=r: new_term = b - tri(r) + r
  LHS change: 6*new_term + cubic(r+1) - cubic(r)
            = 6*(b - tri(r) + r) + 3*r*(r-1)
            = 6*b - 6*tri(r) + 6*r + 3*r*(r-1)
            = 6*b - 3*r*(r+1) + 6*r + 3*r^2 - 3*r    [using 6*tri(r) = 3*r*(r+1)]
            = 6*b
  RHS change: 6*(r+1)*b - 6*r*b = 6*b  ✓
"""
import math


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    r = (-1 + int(math.isqrt(1 + 8 * b))) // 2
    return r if tri(r) == b else None


if __name__ == "__main__":
    print("=== Form 1: 6*B + r*(r-1)*(r-2) = 6*r*b ===\n")

    all_ok = True
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 666]:
        r = qg(b)
        if r is None:
            continue
        B = sum(b - tri(z) + z for z in range(r))
        lhs = 6 * B + r * (r - 1) * (r - 2)
        rhs = 6 * r * b
        ok = lhs == rhs
        all_ok = all_ok and ok
        print(f"b={b:>3} r={r:>2}: 6*B={6*B:>8}, cubic={r*(r-1)*(r-2):>6}, "
              f"LHS={lhs:>8}, RHS={rhs:>8}, match={ok}")

    print(f"\nAll Form 1 checks passed: {all_ok}")

    print("\n=== Induction step: verify 6*(b-tri(r)+r) + 3*r*(r-1) = 6*b ===\n")

    step_ok = True
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 666]:
        r = qg(b)
        if r is None:
            continue
        for n in range(r):
            new_term = b - tri(n) + n
            cubic_diff = (n + 1) * n * max(n - 1, 0) - n * max(n - 1, 0) * max(n - 2, 0)
            lhs_change = 6 * new_term + cubic_diff
            rhs_change = 6 * b
            ok = lhs_change == rhs_change
            if not ok:
                step_ok = False
                print(f"  FAIL at b={b}, n={n}: lhs_change={lhs_change}, rhs_change={rhs_change}")
        print(f"b={b:>3} r={r}: all induction steps OK")

    print(f"\nAll induction steps passed: {step_ok}")

    print("\n=== Tetrahedral identity (corollary): 6*Sum(tri(z)) = (r-1)*r*(r+1) ===\n")

    tet_ok = True
    for r in range(0, 20):
        actual = 6 * sum(tri(z) for z in range(r))
        formula = (r - 1) * r * (r + 1) if r >= 1 else 0
        ok = actual == formula
        tet_ok = tet_ok and ok
        if r <= 10 or not ok:
            print(f"r={r:>2}: 6*Sum_tri = {actual:>6}, (r-1)*r*(r+1) = {formula:>6}, match={ok}")

    print(f"\nAll tetrahedral checks passed: {tet_ok}")

    print("\n=== Key sub-identity: 6*tri(n) = 3*n*(n+1) ===\n")
    for n in range(10):
        lhs = 6 * tri(n)
        rhs = 3 * n * (n + 1)
        print(f"n={n}: 6*tri({n}) = {lhs}, 3*{n}*{n+1} = {rhs}, match={lhs == rhs}")
