"""
Step 4B: Induction Proof Mechanics for Arithmetic-Geometric Sum

Detailed analysis of the Lean 4 proof strategy for:
  (b-1)^2 * Sum_{i<n} i*b^i + n*b^n = (n-1)*b^(n+1) + b

Key findings:
  1. Need hn : 1 <= n (n=0 underflows on RHS)
  2. Do NOT need hb (identity holds for all b in Nat when n >= 1)
  3. ring CANNOT prove (b-1)^2 identities in Nat because (0-1)^2 = 0 in Nat but 1 in Z
  4. Solution: cases on b first (b=0 trivial), then b=c+1 makes (b-1)^2 = c^2
  5. Step lemma is ring-provable after b = c+1 substitution

Sections:
  1. Base case verification
  2. Step lemma derivation and verification
  3. Nat (b-1)^2 edge case analysis
  4. Option A: cases b strategy (RECOMMENDED)
  5. Full proof chain verification
  6. omega atom analysis
"""


def S(b, n):
    """Sum_{i=0}^{n-1} i * b^i"""
    return sum(i * (b ** i) for i in range(n))


if __name__ == "__main__":

    # ================================================================
    # 1. BASE CASE: n=1 (m=0)
    # ================================================================
    print("=" * 70)
    print("1. BASE CASE: n=1 (m=0)")
    print("=" * 70)
    print()
    print("S(1) = 0, so LHS = 0 + b = b, RHS = 0*b^2 + b = b")
    print()

    base_ok = True
    for b in [0, 1, 2, 3, 5, 10, 100]:
        lhs = (b - 1) ** 2 * S(b, 1) + 1 * b ** 1
        rhs = 0 * b ** 2 + b
        ok = lhs == rhs == b
        base_ok = base_ok and ok
        print(f"  b={b:>3}: LHS={lhs:>4} RHS={rhs:>4} ok={ok}")

    print(f"\nBase case verified: {base_ok}")

    # ================================================================
    # 2. STEP LEMMA DERIVATION
    # ================================================================
    print()
    print("=" * 70)
    print("2. STEP LEMMA DERIVATION")
    print("=" * 70)
    print()
    print("After induction on n (succ m), cases m (succ k):")
    print("  IH: (b-1)^2 * S(k+1) + (k+1)*b^(k+1) = k*b^(k+2) + b")
    print("  Goal: (b-1)^2 * S(k+2) + (k+2)*b^(k+2) = (k+1)*b^(k+3) + b")
    print()
    print("After sum_range_succ + mul_add, goal becomes:")
    print("  (b-1)^2*S(k+1) + (b-1)^2*(k+1)*b^(k+1) + (k+2)*b^(k+2)")
    print("  = (k+1)*b^(k+3) + b")
    print()
    print("Adding (k+1)*b^(k+1) to both sides and using IH:")
    print("  [k*b^(k+2) + b] + (b-1)^2*(k+1)*b^(k+1) + (k+2)*b^(k+2)")
    print("  = (k+1)*b^(k+3) + b + (k+1)*b^(k+1)")
    print()
    print("Canceling +b from both sides:")
    print("STEP LEMMA:")
    print("  k*b^(k+2) + (b-1)^2*(k+1)*b^(k+1) + (k+2)*b^(k+2)")
    print("  = (k+1)*b^(k+3) + (k+1)*b^(k+1)")
    print()

    step_ok = True
    for b in [0, 1, 2, 3, 5, 10, 15]:
        for k in range(8):
            lhs = k * b ** (k + 2) + (b - 1) ** 2 * (k + 1) * b ** (k + 1) + (k + 2) * b ** (k + 2)
            rhs = (k + 1) * b ** (k + 3) + (k + 1) * b ** (k + 1)
            ok = lhs == rhs
            step_ok = step_ok and ok
            if not ok:
                print(f"  FAIL b={b} k={k}: diff={lhs - rhs}")

    print(f"Step lemma verified for b=0..15, k=0..7: {step_ok}")

    # Algebraic core: factors to (b-1)^2 + 2*b = b^2 + 1
    print()
    print("Core identity (after dividing by (k+1)*b^(k+1) conceptually):")
    print("  (b-1)^2 + 2*b = b^2 + 1")
    core_ok = True
    for b in range(20):
        ok = (b - 1) ** 2 + 2 * b == b ** 2 + 1
        core_ok = core_ok and ok
    print(f"Core identity verified for b=0..19: {core_ok}")

    # ================================================================
    # 3. NAT (b-1)^2 EDGE CASE
    # ================================================================
    print()
    print("=" * 70)
    print("3. NAT (b-1)^2 EDGE CASE ANALYSIS")
    print("=" * 70)
    print()
    print("In Nat: (0-1)^2 = 0 (truncation to 0, then squared)")
    print("In Z:   (0-1)^2 = 1 ((-1)^2 = 1)")
    print("This means ring CANNOT prove (b-1)^2 identities in Nat!")
    print()

    for b in range(5):
        nat_sq = (max(b - 1, 0)) ** 2
        z_sq = (b - 1) ** 2
        print(f"  b={b}: Nat(b-1)^2={nat_sq}, Z(b-1)^2={z_sq}, same={nat_sq == z_sq}")

    print()
    print("Main theorem at b=0 (Nat truncation):")
    for n in range(1, 6):
        # In Nat: (0-1)^2 = 0, 0^n = 0 for n>=1
        lhs = 0 * S(0, n) + n * 0 ** n
        rhs_nat = max(n - 1, 0) * 0 ** (n + 1) + 0
        print(f"  n={n}: LHS={lhs} RHS={rhs_nat} ok={lhs == rhs_nat}")
    print("Both sides are 0 for all n >= 1 when b = 0. Theorem holds trivially.")

    # ================================================================
    # 4. OPTION A: cases b STRATEGY (RECOMMENDED)
    # ================================================================
    print()
    print("=" * 70)
    print("4. OPTION A: cases b (RECOMMENDED)")
    print("=" * 70)
    print()
    print("cases b with")
    print("| zero => simp  -- both sides 0")
    print("| succ c =>")
    print("  -- Now (b-1)^2 = c^2, ring works!")
    print()
    print("Step lemma with b = c+1:")
    print("  k*(c+1)^(k+2) + c^2*(k+1)*(c+1)^(k+1) + (k+2)*(c+1)^(k+2)")
    print("  = (k+1)*(c+1)^(k+3) + (k+1)*(c+1)^(k+1)")
    print()

    opt_a_ok = True
    for c in range(12):
        for k in range(8):
            b = c + 1
            lhs = k * b ** (k + 2) + c ** 2 * (k + 1) * b ** (k + 1) + (k + 2) * b ** (k + 2)
            rhs = (k + 1) * b ** (k + 3) + (k + 1) * b ** (k + 1)
            ok = lhs == rhs
            opt_a_ok = opt_a_ok and ok
            if not ok:
                print(f"  FAIL c={c} k={k}: diff={lhs - rhs}")

    print(f"Option A step lemma verified for c=0..11, k=0..7: {opt_a_ok}")
    print("ring can prove this: all terms are non-negative polynomials in c, k")

    # ================================================================
    # 5. FULL PROOF CHAIN VERIFICATION
    # ================================================================
    print()
    print("=" * 70)
    print("5. FULL PROOF CHAIN")
    print("=" * 70)
    print()

    chain_ok = True
    for b in [0, 1, 2, 3, 5, 10, 15]:
        for n in range(1, 9):
            # Main theorem at this (b, n)
            lhs = (b - 1) ** 2 * S(b, n) + n * b ** n
            rhs = (n - 1) * b ** (n + 1) + b
            ok = lhs == rhs
            chain_ok = chain_ok and ok
            if not ok:
                print(f"  FAIL b={b} n={n}: LHS={lhs} RHS={rhs}")
        print(f"  b={b:>2}: n=1..8 all OK")

    print(f"\nFull chain verified: {chain_ok}")

    # ================================================================
    # 6. OMEGA ATOM ANALYSIS
    # ================================================================
    print()
    print("=" * 70)
    print("6. OMEGA ATOM ANALYSIS")
    print("=" * 70)
    print()
    print("After rw [sum_range_succ, mul_add] and have hstep := by ring:")
    print()
    print("omega will see these opaque atoms (for b = c+1, n = k+2):")
    print("  A1 = (Finset.range (k+1)).sum (fun i => i * (c+1)^i)  [= S(k+1)]")
    print("  A2 = c^2 * A1                                          [= (b-1)^2 * S(k+1)]")
    print("  A3 = (k+1) * (c+1)^(k+1)                              [common term]")
    print("  A4 = c^2 * A3                                          [= (b-1)^2 * (k+1)*b^(k+1)]")
    print("  A5 = (k+2) * (c+1)^(k+2)                              [goal LHS last term]")
    print("  A6 = k * (c+1)^(k+2)                                   [IH RHS first term]")
    print("  A7 = (k+1) * (c+1)^(k+3)                              [goal RHS first term]")
    print()
    print("IH:   A2 + A3 = A6 + b                   [with b = c+1]")
    print("Step: A6 + A4 + A5 = A7 + A3             [from ring]")
    print("Goal: A2 + A4 + A5 = A7 + b")
    print()
    print("omega derives: (A2 + A3) + (A6 + A4 + A5) = (A6 + b) + (A7 + A3)")
    print("  => A2 + A4 + A5 + A3 + A6 = A6 + A7 + A3 + b")
    print("  => A2 + A4 + A5 = A7 + b  [cancel A3, A6]")
    print("  => Goal. QED.")
    print()
    print("KEY INSIGHT: omega can combine IH and step lemma by linear combination.")
    print("The A3 and A6 terms appear on both sides and cancel cleanly.")
    print()

    # Verify the linear combination works numerically
    lc_ok = True
    for c in range(10):
        b = c + 1
        for k in range(7):
            A1 = S(b, k + 1)
            A2 = c ** 2 * A1
            A3 = (k + 1) * b ** (k + 1)
            A4 = c ** 2 * A3
            A5 = (k + 2) * b ** (k + 2)
            A6 = k * b ** (k + 2)
            A7 = (k + 1) * b ** (k + 3)

            ih_lhs = A2 + A3
            ih_rhs = A6 + b
            step_lhs = A6 + A4 + A5
            step_rhs = A7 + A3
            goal_lhs = A2 + A4 + A5
            goal_rhs = A7 + b

            ih_ok = ih_lhs == ih_rhs
            step_ok2 = step_lhs == step_rhs
            goal_ok = goal_lhs == goal_rhs
            combo = ih_ok and step_ok2 and goal_ok
            lc_ok = lc_ok and combo
            if not combo:
                print(f"  FAIL c={c} k={k}: ih={ih_ok} step={step_ok2} goal={goal_ok}")

    print(f"omega linear combination verified for c=0..9, k=0..6: {lc_ok}")

    # ================================================================
    # SUMMARY
    # ================================================================
    print()
    print("=" * 70)
    print("SUMMARY: LEAN 4 PROOF STRATEGY")
    print("=" * 70)
    print()
    print("theorem arith_geom_sum (b n : Nat) (hn : 1 <= n) :")
    print("    (b - 1) ^ 2 * (Finset.range n).sum (fun i => i * b ^ i) + n * b ^ n =")
    print("    (n - 1) * b ^ (n + 1) + b := by")
    print("  cases b with")
    print("  | zero => simp [Finset.sum_eq_zero (fun i _ => by simp)]")
    print("  | succ c =>")
    print("    induction n with")
    print("    | zero => omega")
    print("    | succ m ih =>")
    print("      cases m with")
    print("      | zero => simp")
    print("      | succ k =>")
    print("        rw [Finset.sum_range_succ, mul_add]")
    print("        have hstep : k*(c+1)^(k+2) + c^2*(k+1)*(c+1)^(k+1) + (k+2)*(c+1)^(k+2)")
    print("                   = (k+1)*(c+1)^(k+3) + (k+1)*(c+1)^(k+1) := by ring")
    print("        omega")
    print()
    print("ESTIMATED BUILD ITERATIONS: 2-4")
    print("  - ring/omega atom matching may need show adjustments")
    print("  - sum_range_succ/mul_add rewrite order matters")
    print("  - b=0 case may need explicit Finset.sum simplification")
    print()

    overall = base_ok and step_ok and core_ok and opt_a_ok and chain_ok and lc_ok
    print(f"{'=' * 70}")
    print(f"STEP 4B PROOF MECHANICS: {'ALL PASSED' if overall else 'FAILURES DETECTED'}")
    print(f"{'=' * 70}")
