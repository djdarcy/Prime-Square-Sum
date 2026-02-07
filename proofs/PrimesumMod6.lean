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
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

  UPDATE: This sketch is now fully formalized in Part 7 below, using
  Mathlib's Nat.nth for the nth prime (via Mathlib.Data.Nat.Prime.Nth)
  and prime_sq_mod_six from Part 6.
-/

-- ============================================================
-- PART 6: General theorem — p² ≡ 1 (mod 6) for all primes p > 3
-- ============================================================

/--
  For every prime p > 3, p² ≡ 1 (mod 6).

  Proof: Since p is prime and p > 3, we have p ≠ 2 and p ≠ 3.
  By primality, 2 ∤ p and 3 ∤ p, which forces p % 6 ∈ {1, 5}.
  In both cases, p² % 6 = 1 (by sq_6k_plus_1_mod6 and sq_6k_plus_5_mod6).
-/
theorem prime_sq_mod_six (p : Nat) (hp : Nat.Prime p) (hgt : p > 3) :
    p ^ 2 % 6 = 1 := by
  -- Step 1: p is not divisible by 2 or 3
  have h2 : ¬(2 ∣ p) := by
    intro hdvd; have := hp.eq_one_or_self_of_dvd 2 hdvd; omega
  have h3 : ¬(3 ∣ p) := by
    intro hdvd; have := hp.eq_one_or_self_of_dvd 3 hdvd; omega
  -- Step 2: Case split on p % 6 — eliminate 0,2,3,4, leaving 1 and 5
  set r := p % 6 with hr_def
  have hlt : r < 6 := Nat.mod_lt p (by omega)
  have hp_eq : p = 6 * (p / 6) + r := by omega
  interval_cases r
  -- r=0: 6∣p so 2∣p, contradiction
  · exfalso; exact h2 ⟨3 * (p / 6), by omega⟩
  -- r=1: p = 6q+1, apply sq_6k_plus_1_mod6
  · rw [hp_eq]; exact sq_6k_plus_1_mod6 _
  -- r=2: 2∣p, contradiction
  · exfalso; exact h2 ⟨3 * (p / 6) + 1, by omega⟩
  -- r=3: 3∣p, contradiction
  · exfalso; exact h3 ⟨2 * (p / 6) + 1, by omega⟩
  -- r=4: 2∣p, contradiction
  · exfalso; exact h2 ⟨3 * (p / 6) + 2, by omega⟩
  -- r=5: p = 6q+5, apply sq_6k_plus_5_mod6
  · rw [hp_eq]; exact sq_6k_plus_5_mod6 _

-- ============================================================
-- PART 7: The general primesum(n, 2) ≡ (n + 5) (mod 6) theorem
-- ============================================================

/-- The nth prime (0-indexed): nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, ... -/
noncomputable def nthPrime (n : Nat) : Nat := Nat.nth Nat.Prime n

/-- Sum of first n primes each raised to `power`.
    primesumN n 2 = Σ_{i=0}^{n-1} (nthPrime i)² -/
noncomputable def primesumN (n : Nat) (power : Nat) : Nat :=
  (Finset.range n).sum (fun i => nthPrime i ^ power)

-- Helper: nthPrime n is always prime
theorem nthPrime_prime (n : Nat) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

-- Helper: nthPrime is strictly monotone
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

-- Helper: nthPrime n > 3 for n ≥ 2
theorem nthPrime_gt_three (n : Nat) (hn : n ≥ 2) : nthPrime n > 3 := by
  have h5 : nthPrime 2 = 5 := Nat.nth_prime_two_eq_five
  have hle : nthPrime 2 ≤ nthPrime n := nthPrime_strictMono.monotone hn
  omega

-- Helper: primesumN unfolds one step
theorem primesumN_succ (n power : Nat) :
    primesumN (n + 1) power = primesumN n power + nthPrime n ^ power := by
  simp [primesumN, Finset.sum_range_succ]

/--
  THEOREM (General): primesum(n, 2) ≡ (n + 5) (mod 6) for all n ≥ 2.

  Proof by induction on n:
    Base (n=2): primesumN 2 2 = 2² + 3² = 13, and 13 % 6 = 1 = (2+5) % 6.
    Step (n→n+1): primesumN (n+1) 2 = primesumN n 2 + nthPrime(n)².
      For n ≥ 2, nthPrime(n) > 3, so nthPrime(n)² % 6 = 1 by prime_sq_mod_six.
      Therefore (primesumN n 2 + 1) % 6 = ((n+5) + 1) % 6 = ((n+1)+5) % 6.
-/
theorem primesumN_mod6 (n : Nat) (hn : n ≥ 2) :
    primesumN n 2 % 6 = (n + 5) % 6 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [primesumN_succ]
    -- Goal: (primesumN k 2 + nthPrime k ^ 2) % 6 = (k + 1 + 5) % 6
    cases k with
    | zero => omega
    | succ j =>
      cases j with
      | zero =>
        -- k = 1, n = 2: base case (primesumN 1 2 + nthPrime 1 ^ 2 = 4 + 9 = 13)
        simp only [primesumN, nthPrime]
        norm_num
      | succ i =>
        -- k = i + 2, n = i + 3
        have ih_applied : primesumN (i + 2) 2 % 6 = (i + 2 + 5) % 6 := ih (by omega)
        have hp := nthPrime_prime (i + 2)
        have hgt := nthPrime_gt_three (i + 2) (by omega)
        have hsq : nthPrime (i + 2) ^ 2 % 6 = 1 := prime_sq_mod_six _ hp hgt
        rw [Nat.add_mod, ih_applied, hsq]
        omega

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

  3. FULLY PROVEN (Part 6 — primality + interval_cases):
     For all primes p > 3, p² ≡ 1 (mod 6)

  4. FULLY PROVEN (Part 7 — induction via Nat.nth + Finset.sum):
     primesum(n,2) ≡ (n+5) (mod 6) for all n ≥ 2

  5. COROLLARY:
     primesum(n,2) divisible by 6 iff n = 1 (mod 6)

  6. APPLICATION:
     For stf(b) = primesum(n,2) to hold, n must satisfy n = 1 (mod 6).
     Combined with the stf-k^2 conjecture (r = k^2 required for 6 | stf(b)),
     this provides a necessary condition filtering the search space.
-/
