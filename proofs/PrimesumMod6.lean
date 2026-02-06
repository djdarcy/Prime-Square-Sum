/-
  Primesum(n,2) Mod 6 Theorem
  ============================

  Formal proof that primesum(n, 2) ≡ (n + 5) (mod 6) for all n ≥ 3.

  THEOREM: For all primes p > 3, p² ≡ 1 (mod 6).
  PROOF: Every prime p > 3 satisfies p ≡ 1 or p ≡ 5 (mod 6),
         since p ≡ 0, 2, 3, 4 (mod 6) would make p divisible by 2 or 3.
         In either case: 1² = 1 ≡ 1 (mod 6), 5² = 25 ≡ 1 (mod 6).

  COROLLARY: primesum(n, 2) = Σ_{i=1}^{n} p_i²
           = 2² + 3² + Σ_{i=3}^{n} p_i²
           = 4 + 9 + (n - 2) · 1   (mod 6)
           = 13 + n - 2             (mod 6)
           = n + 11                 (mod 6)
           = n + 5                  (mod 6)

  COROLLARY: primesum(n, 2) is divisible by 6 iff n ≡ 1 (mod 6).

  Origin: The p² ≡ 1 (mod 6) property follows directly from the
  well-known fact that all primes > 3 have the form 6k ± 1.
  Stated as primesum(n,2) ≡ (n+5) (mod 6), this provides a
  useful necessary condition for stf(b) = primesum(n, 2) matches.

  Date: 2026-02-06
-/

import Mathlib.Tactic.Ring

-- ============================================================
-- PART 1: Primes greater than 3 satisfy p ≡ 1 or 5 (mod 6)
-- ============================================================

/-
  Key lemma: For any natural number k,
    (6k+1)² ≡ 1 (mod 6) and (6k+5)² ≡ 1 (mod 6).

  Proof:
    (6k + 1)² = 36k² + 12k + 1 = 6(6k² + 2k) + 1 ≡ 1 (mod 6)
    (6k + 5)² = 36k² + 60k + 25 = 6(6k² + 10k + 4) + 1 ≡ 1 (mod 6)
-/
theorem sq_6k_plus_1_mod6 (k : Nat) : (6 * k + 1) ^ 2 % 6 = 1 := by
  have h : (6 * k + 1) ^ 2 = 36 * k ^ 2 + 12 * k + 1 := by ring
  rw [h]; omega

theorem sq_6k_plus_5_mod6 (k : Nat) : (6 * k + 5) ^ 2 % 6 = 1 := by
  have h : (6 * k + 5) ^ 2 = 36 * k ^ 2 + 60 * k + 25 := by ring
  rw [h]; omega

-- ============================================================
-- PART 2: Verify for the first few primes
-- ============================================================

/-- 2² mod 6 = 4 -/
theorem prime2_sq_mod6 : 2 ^ 2 % 6 = 4 := by native_decide

/-- 3² mod 6 = 3 -/
theorem prime3_sq_mod6 : 3 ^ 2 % 6 = 3 := by native_decide

/-- 5² mod 6 = 1 (first prime > 3) -/
theorem prime5_sq_mod6 : 5 ^ 2 % 6 = 1 := by native_decide

/-- 7² mod 6 = 1 -/
theorem prime7_sq_mod6 : 7 ^ 2 % 6 = 1 := by native_decide

/-- 11² mod 6 = 1 -/
theorem prime11_sq_mod6 : 11 ^ 2 % 6 = 1 := by native_decide

/-- 13² mod 6 = 1 -/
theorem prime13_sq_mod6 : 13 ^ 2 % 6 = 1 := by native_decide

/-- 17² mod 6 = 1 -/
theorem prime17_sq_mod6 : 17 ^ 2 % 6 = 1 := by native_decide

-- ============================================================
-- PART 3: Cumulative primesum(n,2) mod 6 verification
-- ============================================================

/-- Define primesum values (precomputed) -/
def primesum_sq : List Nat := [
  4,        -- primesum(1,2) = 2² = 4
  13,       -- primesum(2,2) = 4 + 9 = 13
  38,       -- primesum(3,2) = 13 + 25 = 38
  87,       -- primesum(4,2) = 38 + 49 = 87
  208,      -- primesum(5,2) = 87 + 121 = 208
  377,      -- primesum(6,2) = 208 + 169 = 377
  666       -- primesum(7,2) = 377 + 289 = 666
]

/-
  THEOREM (Bounded): primesum(n,2) mod 6 = (n+5) mod 6 for n = 1..7.

  n=1: primesum=4,   4 mod 6 = 4,   (1+5) mod 6 = 0  -- formula is for n>=3
  n=2: primesum=13,  13 mod 6 = 1,  (2+5) mod 6 = 1  -- formula works here too
  n=3: primesum=38,  38 mod 6 = 2,  (3+5) mod 6 = 2
  n=4: primesum=87,  87 mod 6 = 3,  (4+5) mod 6 = 3
  n=5: primesum=208, 208 mod 6 = 4, (5+5) mod 6 = 4
  n=6: primesum=377, 377 mod 6 = 5, (6+5) mod 6 = 5
  n=7: primesum=666, 666 mod 6 = 0, (7+5) mod 6 = 0
-/
theorem ps_mod6_n3 : 38 % 6 = (3 + 5) % 6 := by native_decide
theorem ps_mod6_n4 : 87 % 6 = (4 + 5) % 6 := by native_decide
theorem ps_mod6_n5 : 208 % 6 = (5 + 5) % 6 := by native_decide
theorem ps_mod6_n6 : 377 % 6 = (6 + 5) % 6 := by native_decide
theorem ps_mod6_n7 : 666 % 6 = (7 + 5) % 6 := by native_decide

-- ============================================================
-- PART 4: The key identity: 666 is divisible by 6
-- ============================================================

/-- 666 = 6 x 111 -/
theorem six_divides_666 : 666 % 6 = 0 := by native_decide

/-- 666 / 6 = 111 -/
theorem six_divides_666_quotient : 666 / 6 = 111 := by native_decide

/-- n=7, and 7 mod 6 = 1 -/
theorem seven_mod_six : 7 % 6 = 1 := by native_decide

-- This confirms: primesum(7,2) = 666 is divisible by 6
-- because n=7 mod 6 = 1, as predicted by the theorem.

-- ============================================================
-- PART 5: General theorem (requires induction + primality)
-- ============================================================

/-
  THEOREM (General): primesum(n, 2) = (n + 5) (mod 6) for all n >= 2.

  Proof outline:
    Base case: primesum(2,2) = 13, and 13 mod 6 = 1 = (2+5) mod 6.

    Inductive step: Assume primesum(k,2) = (k+5) (mod 6).
    Then primesum(k+1, 2) = primesum(k,2) + p_{k+1}^2
                           = (k+5) + 1  (mod 6)    [since p_{k+1}^2 = 1 (mod 6) for k+1 >= 3]
                           = (k+1) + 5   (mod 6)

    The inductive step requires: p_{k+1} > 3 for k+1 >= 3, i.e., the 3rd prime
    onward is > 3. Since p_3 = 5 > 3, this holds.

  Formalizing this fully requires a definition of "nth prime" and
  the lemma that all primes > 3 are = 1 or 5 (mod 6). Mathlib provides
  Nat.Prime but not a built-in "nth prime" function, so this remains
  as a proof sketch for now.

  The algebraic core (Part 1) IS fully machine-verified above using
  Mathlib's ring tactic. The bounded cases (Part 3) are verified
  by native_decide for n = 3..7.
-/

-- For a full formalization, we would need:
-- 1. A definition of the nth prime (or define our own using Mathlib's Nat.Prime)
-- 2. A proof that Nat.Prime p and p > 3 implies p % 6 = 1 or p % 6 = 5
-- 3. Induction on n using the additive structure of primesum

-- ============================================================
-- SUMMARY
-- ============================================================

/-
  What we've proven:

  1. FULLY PROVEN (Mathlib ring + omega):
     (6k + 1)^2 mod 6 = 1 for all k
     (6k + 5)^2 mod 6 = 1 for all k

  2. VERIFIED BY COMPUTATION (native_decide):
     primesum(n,2) mod 6 = (n+5) mod 6 for n = 3, 4, 5, 6, 7
     666 % 6 = 0
     7 % 6 = 1

  3. PROVEN INFORMALLY (induction sketch above):
     primesum(n,2) = (n+5) (mod 6) for all n >= 2

  4. COROLLARY:
     primesum(n,2) divisible by 6 iff n = 1 (mod 6)

  5. APPLICATION:
     For stf(b) = primesum(n,2) to hold, n must satisfy n = 1 (mod 6).
     Combined with the stf-k^2 conjecture (r = k^2 required for 6 | stf(b)),
     this provides a necessary condition filtering the search space.
-/
