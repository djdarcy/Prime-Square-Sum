"""
Step 4B: Step Lemma Derivation

Derives the correct Nat-safe additive step lemma for the arithmetic-geometric
sum induction proof. This script was created during the dev-workflow analysis
when the first attempt at a step lemma was found to be WRONG.

Key derivation:
  1. Start from IH and Goal in Z-arithmetic
  2. Subtract IH from Goal to get the step equation
  3. Move negative terms to opposite sides for Nat safety
  4. Verify the result simplifies to (b-1)^2 + 2b = b^2 + 1

Result:
  STEP LEMMA (Z form):
    (b-1)^2*(m+1)*b^(m+1) + (m+2)*b^(m+2) - (m+1)*b^(m+1) = (m+1)*b^(m+3) - m*b^(m+2)

  STEP LEMMA (Nat-safe, simplified):
    (b-1)^2*(m+1)*b^(m+1) + 2*(m+1)*b^(m+2) = (m+1)*b^(m+3) + (m+1)*b^(m+1)
"""


if __name__ == "__main__":

    # ================================================================
    # 1. Z-FORM STEP LEMMA
    # ================================================================
    print("=" * 70)
    print("1. STEP LEMMA (Z-form)")
    print("=" * 70)
    print()
    print("Derived by subtracting IH from Goal:")
    print("  (b-1)^2*(m+1)*b^(m+1) + (m+2)*b^(m+2) - (m+1)*b^(m+1)")
    print("  = (m+1)*b^(m+3) - m*b^(m+2)")
    print()

    z_ok = True
    for b in [0, 1, 2, 3, 5, 10]:
        for m in range(6):
            lhs = (b - 1) ** 2 * (m + 1) * b ** (m + 1) + (m + 2) * b ** (m + 2) - (m + 1) * b ** (m + 1)
            rhs = (m + 1) * b ** (m + 3) - m * b ** (m + 2)
            ok = lhs == rhs
            z_ok = z_ok and ok
            if not ok:
                print(f"  FAIL b={b} m={m}: lhs={lhs} rhs={rhs}")

    print(f"Z-form verified: {z_ok}")

    # ================================================================
    # 2. NAT-SAFE FORM (move negatives to opposite sides)
    # ================================================================
    print()
    print("=" * 70)
    print("2. NAT-SAFE FORM")
    print("=" * 70)
    print()
    print("Move -(m+1)*b^(m+1) to RHS, -m*b^(m+2) to LHS:")
    print("  (b-1)^2*(m+1)*b^(m+1) + (m+2)*b^(m+2) + m*b^(m+2)")
    print("  = (m+1)*b^(m+3) + (m+1)*b^(m+1)")
    print()
    print("Simplify: (m+2)*b^(m+2) + m*b^(m+2) = (2m+2)*b^(m+2) = 2*(m+1)*b^(m+2)")
    print()
    print("FINAL NAT-SAFE FORM:")
    print("  (b-1)^2*(m+1)*b^(m+1) + 2*(m+1)*b^(m+2)")
    print("  = (m+1)*b^(m+3) + (m+1)*b^(m+1)")
    print()

    nat_ok = True
    for b in [0, 1, 2, 3, 5, 10, 15]:
        for m in range(8):
            lhs = (b - 1) ** 2 * (m + 1) * b ** (m + 1) + 2 * (m + 1) * b ** (m + 2)
            rhs = (m + 1) * b ** (m + 3) + (m + 1) * b ** (m + 1)
            ok = lhs == rhs
            nat_ok = nat_ok and ok
            if not ok:
                print(f"  FAIL b={b} m={m}: diff={lhs - rhs}")

    print(f"Nat-safe form verified: {nat_ok}")

    # ================================================================
    # 3. CORE ALGEBRAIC IDENTITY
    # ================================================================
    print()
    print("=" * 70)
    print("3. CORE ALGEBRAIC IDENTITY")
    print("=" * 70)
    print()
    print("Factor (m+1)*b^(m+1) from both sides:")
    print("  (b-1)^2 + 2*b = b^2 + 1")
    print("  b^2 - 2b + 1 + 2b = b^2 + 1  YES!")
    print()

    core_ok = True
    for b in range(20):
        ok = (b - 1) ** 2 + 2 * b == b ** 2 + 1
        core_ok = core_ok and ok
    print(f"Core identity verified for b=0..19: {core_ok}")

    # ================================================================
    # 4. CONTEXT: WHY THE FIRST ATTEMPT FAILED
    # ================================================================
    print()
    print("=" * 70)
    print("4. WHY THE FIRST ATTEMPT FAILED")
    print("=" * 70)
    print()
    print("First attempt step lemma was:")
    print("  (b-1)^2*(m+1)*b^(m+1) + (m+2)*b^(m+2) + (m+1)*b^(m+1) + b")
    print("  = (m+1)*b^(m+3) + m*b^(m+2) + b")
    print()
    print("This is WRONG because it conflated the step lemma with the IH.")
    print("The correct approach: derive step = Goal - IH, then make Nat-safe.")
    print()

    first_ok = True
    for b in [2, 3, 5, 10]:
        for m in range(5):
            lhs = (b - 1) ** 2 * (m + 1) * b ** (m + 1) + (m + 2) * b ** (m + 2) + (m + 1) * b ** (m + 1) + b
            rhs = (m + 1) * b ** (m + 3) + m * b ** (m + 2) + b
            ok = lhs == rhs
            first_ok = first_ok and ok
            if not ok:
                print(f"  FAIL b={b} m={m}: diff={lhs - rhs}")

    if first_ok:
        print("Hmm, first attempt actually DOES hold in Z... but the formulation")
        print("was wrong for the Lean proof structure (mixed IH terms into step).")
    else:
        print(f"First attempt verified: {first_ok}")

    # ================================================================
    # SUMMARY
    # ================================================================
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("The correct step lemma for Lean 4 is:")
    print()
    print("  In the induction body (after cases b => succ c):")
    print("  have hstep : k*(c+1)^(k+2) + c^2*(k+1)*(c+1)^(k+1) + (k+2)*(c+1)^(k+2)")
    print("             = (k+1)*(c+1)^(k+3) + (k+1)*(c+1)^(k+1) := by ring")
    print()
    print("  This is the same identity as above, with b = c+1 and (b-1)^2 = c^2,")
    print("  expanded into terms that ring can handle without Nat subtraction issues.")

    overall = z_ok and nat_ok and core_ok
    print()
    print(f"{'=' * 70}")
    print(f"STEP LEMMA DERIVATION: {'ALL PASSED' if overall else 'FAILURES DETECTED'}")
    print(f"{'=' * 70}")
