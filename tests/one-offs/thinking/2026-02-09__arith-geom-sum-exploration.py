"""
Step 4B Groundwork: Arithmetic-Geometric Sum Exploration

Consolidated from 6 inline scripts run on 2026-02-09 00:48-00:50 during
the postmortem session after Step 4A completion.

Explores the identity:
  (b-1)^2 * Sum_{i=0}^{n-1} i*b^i + n*b^n = (n-1)*b^(n+1) + b

This is the Nat-safe additive form (no subtraction in the conclusion).
The identity is the mathematical bottleneck for Step 4B.

Sections:
  1. Full identity verification (both standard and Nat-safe forms)
  2. Intermediate factoring: (b-1) * Sum = n*b^n - b*Sum(b^i)
  3. Induction step structure analysis
  4. Summary of Lean 4 proof strategy
"""
import math


def arith_geom_sum(b, n):
    """Sum_{i=0}^{n-1} i * b^i"""
    return sum(i * (b ** i) for i in range(n))


def geom_sum(b, n):
    """Sum_{i=0}^{n-1} b^i"""
    return sum(b ** i for i in range(n))


if __name__ == "__main__":

    # ================================================================
    # 1. FULL IDENTITY VERIFICATION
    # ================================================================
    print("=" * 70)
    print("1. ARITHMETIC-GEOMETRIC SUM IDENTITY VERIFICATION")
    print("=" * 70)
    print()
    print("Nat-safe form: (b-1)^2 * S(n) + n*b^n = (n-1)*b^(n+1) + b")
    print("Standard form: (b-1)^2 * S(n) = (n-1)*b^(n+1) - n*b^n + b")
    print()

    all_pass = True
    bases = [2, 3, 6, 10, 15]
    n_values = range(9)  # 0..8

    for b in bases:
        print(f"Base b = {b}:")
        for n in n_values:
            s = arith_geom_sum(b, n)

            # Standard form
            lhs_std = (b - 1) ** 2 * s
            rhs_std = (n - 1) * (b ** (n + 1)) - n * (b ** n) + b

            # Nat-safe additive form
            lhs_nat = (b - 1) ** 2 * s + n * (b ** n)
            rhs_nat = (n - 1) * (b ** (n + 1)) + b

            std_ok = lhs_std == rhs_std
            nat_ok = lhs_nat == rhs_nat
            all_pass = all_pass and std_ok and nat_ok

            if not (std_ok and nat_ok):
                print(f"  n={n}: FAIL  std={std_ok} nat={nat_ok}")
            else:
                print(f"  n={n}: S(n)={s:8d}  Std: OK  Nat-safe: OK")

    print(f"\nAll identity checks passed: {all_pass}")

    # ================================================================
    # 2. INTERMEDIATE FACTORING: (b-1) * sum = n*b^n - b*Sum(b^i)
    # ================================================================
    print()
    print("=" * 70)
    print("2. INTERMEDIATE: (b-1) * Sum i*b^i = n*b^n - b*Sum(b^i)")
    print("=" * 70)
    print()

    inter_ok = True
    for b in [2, 3, 6, 10]:
        print(f"Base b = {b}:")
        for n in range(1, 7):
            s = arith_geom_sum(b, n)
            g = geom_sum(b, n)

            lhs = (b - 1) * s
            rhs = n * (b ** n) - b * g

            ok = lhs == rhs
            inter_ok = inter_ok and ok
            print(f"  n={n}: (b-1)*S = {lhs:8d}, n*b^n - b*G = {rhs:8d}  {'OK' if ok else 'FAIL'}")

    print(f"\nAll intermediate checks passed: {inter_ok}")

    # ================================================================
    # 3. INDUCTION STEP ANALYSIS
    # ================================================================
    print()
    print("=" * 70)
    print("3. INDUCTION STEP VERIFICATION")
    print("=" * 70)
    print()
    print("Given IH: (b-1)^2 * S(n) + n*b^n = (n-1)*b^(n+1) + b")
    print("Goal:     (b-1)^2 * S(n+1) + (n+1)*b^(n+1) = n*b^(n+2) + b")
    print()
    print("Step-by-step:")
    print("  1. S(n+1) = S(n) + n*b^n")
    print("  2. (b-1)^2 * S(n) = (n-1)*b^(n+1) + b - n*b^n  [from IH]")
    print("  3. (b-1)^2 * n*b^n = n*b^(n+2) - 2n*b^(n+1) + n*b^n")
    print("  4. Collect: coeff of b^(n+1) = (n-1) - 2n + (n+1) = 0")
    print("  5. Collect: coeff of b^n = -n + n = 0")
    print("  6. Result: n*b^(n+2) + b")
    print()

    step_ok = True
    for b in [2, 3, 6, 10]:
        print(f"Base b = {b}:")
        for n in range(1, 6):
            s_n = arith_geom_sum(b, n)
            s_n1 = arith_geom_sum(b, n + 1)

            # Verify IH holds at n
            lhs_n = (b - 1) ** 2 * s_n + n * (b ** n)
            rhs_n = (n - 1) * (b ** (n + 1)) + b

            # Verify goal holds at n+1
            lhs_n1 = (b - 1) ** 2 * s_n1 + (n + 1) * (b ** (n + 1))
            rhs_n1 = n * (b ** (n + 2)) + b

            # Compute step-by-step using IH substitution
            ih_substituted = (n - 1) * (b ** (n + 1)) + b - n * (b ** n)
            expansion = (b - 1) ** 2 * n * (b ** n)
            increment = (n + 1) * (b ** (n + 1))
            calc_total = ih_substituted + expansion + increment

            ok = (lhs_n == rhs_n) and (lhs_n1 == rhs_n1) and (calc_total == rhs_n1)
            step_ok = step_ok and ok
            print(f"  n={n}: IH? {lhs_n == rhs_n}  Goal? {lhs_n1 == rhs_n1}  Calc? {calc_total == rhs_n1}")

    print(f"\nAll induction steps passed: {step_ok}")

    # ================================================================
    # 4. KEY EXPANSION VERIFICATION
    # ================================================================
    print()
    print("=" * 70)
    print("4. KEY EXPANSION: (b-1)^2 * n*b^n = n*b^(n+2) - 2n*b^(n+1) + n*b^n")
    print("=" * 70)
    print()

    expand_ok = True
    for b in [2, 3, 6, 10]:
        for n in range(0, 6):
            lhs = (b - 1) ** 2 * n * (b ** n)
            rhs = n * (b ** (n + 2)) - 2 * n * (b ** (n + 1)) + n * (b ** n)
            ok = lhs == rhs
            expand_ok = expand_ok and ok
            if not ok:
                print(f"  FAIL: b={b} n={n}: {lhs} vs {rhs}")

    print(f"All expansion checks passed: {expand_ok}")

    # ================================================================
    # FINAL SUMMARY
    # ================================================================
    print()
    print("=" * 70)
    print("SUMMARY: LEAN 4 PROOF STRATEGY FOR STEP 4B")
    print("=" * 70)
    print()
    print("IDENTITY (Nat-safe additive form):")
    print("  (b-1)^2 * Sum_{i<n} i*b^i + n*b^n = (n-1)*b^(n+1) + b")
    print()
    print("DOMAIN: Valid for all b, n in Nat with n >= 1")
    print("  (n=0: both sides = 0 when b >= 1, but (n-1) underflows)")
    print()
    print("BASE CASE (n=1): S(1) = 0, so LHS = b, RHS = 0 + b = b")
    print()
    print("INDUCTIVE STEP:")
    print("  1. S(n+1) = S(n) + n*b^n")
    print("  2. Expand (b-1)^2 * n*b^n via ring")
    print("  3. Substitute IH for (b-1)^2 * S(n)")
    print("  4. b^(n+1) coefficients cancel: (n-1) - 2n + (n+1) = 0")
    print("  5. b^n coefficients cancel: -n + n = 0")
    print("  6. omega closes: n*b^(n+2) + b = n*b^(n+2) + b")
    print()
    print("LEAN TACTICS: ring + show + omega (same pattern as Step 4A)")
    print("No division required - completely Nat-safe!")
    print()

    overall = all_pass and inter_ok and step_ok and expand_ok
    print(f"{'=' * 70}")
    print(f"STEP 4B EXPLORATION: {'ALL PASSED' if overall else 'FAILURES DETECTED'}")
    print(f"{'=' * 70}")
