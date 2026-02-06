/-
  TriSum and Triangular Number Proofs
  ====================================

  Basic Lean 4 formalizations for concepts from
  "Zero_AG to The Scarcity Framework: A Guide" by D. Darcy

  This file demonstrates how to build up proofs from definitions.
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Parity

-- ============================================================
-- PART 1: Triangular Numbers
-- ============================================================

/-- Definition: The nth triangular number is n(n+1)/2 -/
def tri (n : Nat) : Nat := n * (n + 1) / 2

-- Basic computed values (Lean can evaluate these directly)
#eval tri 1   -- 1
#eval tri 2   -- 3
#eval tri 3   -- 6
#eval tri 4   -- 10
#eval tri 10  -- 55
#eval tri 36  -- 666

/-- Lemma: tri(0) = 0 (base case for induction) -/
theorem tri_zero : tri 0 = 0 := by native_decide

/-- Lemma: tri(1) = 1 -/
theorem tri_one : tri 1 = 1 := by native_decide

/-- Lemma: tri(2) = 3 -/
theorem tri_two : tri 2 = 3 := by native_decide

/-- Lemma: tri(3) = 6 -/
theorem tri_three : tri 3 = 6 := by native_decide

/-- Lemma: tri(4) = 10 (base-10!) -/
theorem tri_four : tri 4 = 10 := by native_decide

/-- Lemma: tri(36) = 666 -/
theorem tri_thirtysix : tri 36 = 666 := by native_decide

/--
  The recursive property: tri(n+1) = tri(n) + (n+1)

  Proof sketch: n*(n+1) is always even (consecutive numbers), so division is exact.
  (n+1)*(n+2)/2 = (n*(n+1) + 2*(n+1))/2 = n*(n+1)/2 + (n+1) = tri(n) + (n+1)

  Full proof requires Mathlib's Nat.div_add_div or manual even/odd case analysis.
-/
theorem tri_succ (n : Nat) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  -- (n+1)*(n+2) = n*(n+1) + (n+1)*2, then apply Nat.add_mul_div_right
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : (0 : Nat) < 2)]

/--
  The division-free formula: 2 * tri(n) = n * (n + 1)

  Proved by induction using tri_zero and tri_succ.
  This avoids Nat division entirely and captures the essential identity.
-/
theorem two_mul_tri (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => simp [tri_zero]
  | succ k ih =>
    rw [tri_succ, Nat.mul_add, ih]
    ring

-- ============================================================
-- PART 2: Checking if a number is triangular
-- ============================================================

/--
  A number t is triangular iff there exists n such that tri(n) = t.
  Equivalently: 8t + 1 must be a perfect square, and (sqrt(8t+1) - 1) / 2 must be natural.
-/
def isTriangular (t : Nat) : Bool :=
  let discriminant := 1 + 8 * t
  let sqrtDisc := Nat.sqrt discriminant
  sqrtDisc * sqrtDisc == discriminant && (sqrtDisc - 1) % 2 == 0

#eval isTriangular 1    -- true  (tri 1)
#eval isTriangular 3    -- true  (tri 2)
#eval isTriangular 6    -- true  (tri 3)
#eval isTriangular 10   -- true  (tri 4)
#eval isTriangular 55   -- true  (tri 10)
#eval isTriangular 666  -- true  (tri 36)
#eval isTriangular 7    -- false
#eval isTriangular 100  -- false

/-- If tri(n) produces t, then t is triangular -/
theorem tri_is_triangular (n : Nat) : isTriangular (tri n) = true := by
  unfold isTriangular tri
  -- Step 1: Prove the discriminant equals the perfect square (2n + 1)²
  have h_disc : 1 + 8 * (n * (n + 1) / 2) = (2 * n + 1) ^ 2 := by
    -- Since n*(n+1) is always even, merge the 8* and /2:
    -- 8 * (x / 2) = 8 * x / 2 (by Nat.mul_div_assoc, applied backwards)
    rw [← Nat.mul_div_assoc _ (Nat.even_mul_succ_self n).two_dvd]
    -- Now: 1 + 8 * (n * (n + 1)) / 2 = (2 * n + 1) ^ 2
    -- Rewrite 8 * (n * (n + 1)) as 2 * (4 * (n * (n + 1))) to cancel /2
    have h8 : 8 * (n * (n + 1)) = 2 * (4 * (n * (n + 1))) := by ring
    rw [h8, Nat.mul_div_cancel_left _ (by norm_num : (0 : Nat) < 2)]
    -- Now: 1 + 4 * (n * (n + 1)) = (2 * n + 1) ^ 2
    ring
  -- Step 2: Substitute the discriminant and simplify
  simp only [h_disc, Nat.sqrt_eq']
  -- Step 3: The boolean conditions reduce to decidable arithmetic
  -- Need: (2n+1)*(2n+1) == (2n+1)^2 && (2n+1-1) % 2 == 0
  simp [Nat.pow_two]

-- ============================================================
-- PART 3: The 5-State XOR Cycle
-- ============================================================

/--
  Logical states as 4-tuples representing truth tables.
  For two variables P, Q, the tuple represents [PQ=TT, PQ=TF, PQ=FT, PQ=FF]
-/
structure LogicState where
  tt : Bool  -- P=T, Q=T
  tf : Bool  -- P=T, Q=F
  ft : Bool  -- P=F, Q=T
  ff : Bool  -- P=F, Q=F
deriving Repr, DecidableEq

/-- G₀: Biconditional (P ↔ Q) = {T, F, F, T} -/
def G0 : LogicState := ⟨true, false, false, true⟩

/-- G₁: XOR (P ⊕ Q) = {F, T, T, F} -/
def G1 : LogicState := ⟨false, true, true, false⟩

/-- E: Tautology = {T, T, T, T} -/
def E : LogicState := ⟨true, true, true, true⟩

/-- F: Contradiction = {F, F, F, F} -/
def F : LogicState := ⟨false, false, false, false⟩

/-- XOR operation on logic states (component-wise) -/
def LogicState.xor (a b : LogicState) : LogicState :=
  ⟨Bool.xor a.tt b.tt, Bool.xor a.tf b.tf, Bool.xor a.ft b.ft, Bool.xor a.ff b.ff⟩

instance : HXor LogicState LogicState LogicState where
  hXor := LogicState.xor

-- ============================================================
-- PART 4: Proving the 5-State Cycle
-- ============================================================

/-- Step 0: Start with G₀ -/
def step0 : LogicState := G0

/-- Step 1: G₀ ⊕ G₁ = E (tautology) -/
def step1 : LogicState := G0 ^^^ G1

theorem step1_is_E : step1 = E := by native_decide

/-- Step 2: E ⊕ G₀ = G₁ -/
def step2 : LogicState := step1 ^^^ G0

theorem step2_is_G1 : step2 = G1 := by native_decide

/-- Step 3: G₁ ⊕ G₁ = F (contradiction) -/
def step3 : LogicState := step2 ^^^ G1

theorem step3_is_F : step3 = F := by native_decide

/-- Step 4: F ⊕ G₀ = G₀ (back to start!) -/
def step4 : LogicState := step3 ^^^ G0

theorem step4_is_G0 : step4 = G0 := by native_decide

/--
  THEOREM: The complete cycle returns to G₀

  ((((G₀ ⊕ G₁) ⊕ G₀) ⊕ G₁) ⊕ G₀) = G₀

  This proves the 5-state cycle: G₀ → E → G₁ → F → G₀
-/
theorem xor_cycle_returns : (((G0 ^^^ G1) ^^^ G0) ^^^ G1) ^^^ G0 = G0 := by
  native_decide

/-- The cycle visits exactly these 5 states -/
theorem cycle_states :
  [G0, G0 ^^^ G1, (G0 ^^^ G1) ^^^ G0, ((G0 ^^^ G1) ^^^ G0) ^^^ G1,
   (((G0 ^^^ G1) ^^^ G0) ^^^ G1) ^^^ G0] = [G0, E, G1, F, G0] := by
  native_decide

-- ============================================================
-- PART 5: The 5-and-2 Pattern
-- ============================================================

/--
  The number of distinct states in the cycle (before returning to start).
  We have: G₀, E, G₁, F = 4 distinct states
  But the SEQUENCE has 5 positions: G₀ → E → G₁ → F → G₀
-/
def cycleLength : Nat := 5
def distinctStates : Nat := 4
def numConstants : Nat := 2  -- G₀ and G₁

/-- Base 10 = 2 × 5 -/
theorem base_ten_factorization : 10 = 2 * 5 := by native_decide

/-- tri(4) = 10, connecting triangular numbers to base-10 -/
theorem tri_four_is_ten : tri 4 = 10 := by native_decide

-- ============================================================
-- PART 6: TriSum Pattern (Bounded Theorem)
-- ============================================================

/--
  THEOREM (Bounded): For n ∈ {2, 3, 4}, the recast of TriSum[Tri[n]]
  to base-10 yields a triangular number.

  This is verified computationally; formal proof requires TriSum definition.
-/

-- The key values from our Python verification:
-- n=2: base=3,  TriSum=3,     Recast=10   = Tri[4]   ✓
-- n=3: base=6,  TriSum=35,    Recast=55   = Tri[10]  ✓
-- n=4: base=10, TriSum=666,   Recast=666  = Tri[36]  ✓
-- n=5: base=15, TriSum=24605, Recast=7455 = NOT triangular

theorem recast_n2_triangular : isTriangular 10 = true := by native_decide
theorem recast_n3_triangular : isTriangular 55 = true := by native_decide
theorem recast_n4_triangular : isTriangular 666 = true := by native_decide
theorem recast_n5_NOT_triangular : isTriangular 7455 = false := by native_decide

-- COROLLARY: The pattern breaks at n=5, suggesting base-10 (= 2x5)
-- is a structural boundary.

-- ============================================================
-- PART 7: Deep Triangular Structure
-- ============================================================

/-- For n=3: Recast = 55 = Tri[10] = Tri[Tri[4]] -/
theorem deep_structure_n3 : tri (tri 4) = 55 := by native_decide

/-- For n=4: Recast = 666 = Tri[36] = Tri[Tri[8]] -/
theorem deep_structure_n4 : tri (tri 8) = 666 := by native_decide

-- Observation: The index doubles from 4 to 8 as we go from n=3 to n=4.
-- At n=3: index = 4 = n + 1
-- At n=4: index = 8 = 2n
-- This transition occurs exactly at base-10.

-- ============================================================
-- PART 8: Synthesis — How the Pieces Fit Together
-- ============================================================

/-
  This section demonstrates how the fundamental building blocks compose.
  The dependency chain is:

    tri_zero (base case)
        ↓
    tri_succ (recursion: tri(n+1) = tri(n) + (n+1))
        ↓
    two_mul_tri (induction: 2·tri(n) = n·(n+1))
        ↓
    tri_is_triangular (correctness: isTriangular(tri(n)) = true)
        ↓
    tri_tri_is_triangular (composition: tri(tri(n)) is triangular)
    tri_plus_succ_is_triangular (chaining: tri(n)+(n+1) is triangular)
        ↓
    deep_tri_n3_triangular (55 is triangular because 55 = tri(tri(4)))
    deep_tri_n4_triangular (666 is triangular because 666 = tri(tri(8)))
-/

/-- Composition: tri(tri(n)) is always triangular.
    Proof: tri(tri(n)) is tri applied to a natural number. -/
theorem tri_tri_is_triangular (n : Nat) : isTriangular (tri (tri n)) = true :=
  tri_is_triangular (tri n)

/-- Chaining tri_succ with tri_is_triangular:
    adding (n+1) to tri(n) always yields a triangular number. -/
theorem tri_plus_succ_is_triangular (n : Nat) :
    isTriangular (tri n + (n + 1)) = true := by
  rw [← tri_succ]
  exact tri_is_triangular (n + 1)

/-- 55 is triangular — proved structurally via tri(tri(4)), not by computation. -/
theorem deep_tri_n3_triangular : isTriangular (tri (tri 4)) = true :=
  tri_tri_is_triangular 4

/-- 666 is triangular — proved structurally via tri(tri(8)), not by computation. -/
theorem deep_tri_n4_triangular : isTriangular (tri (tri 8)) = true :=
  tri_tri_is_triangular 8

-- ============================================================
-- SUMMARY
-- ============================================================

/-
  What we've proven:

  1. Triangular number foundations:
     tri_zero, tri_one, ..., tri_thirtysix — basic identities
     tri_succ — recursion: tri(n+1) = tri(n) + (n+1)
     two_mul_tri — division-free formula: 2·tri(n) = n·(n+1)
                   (proved by induction on tri_zero + tri_succ)

  2. Correctness bridge:
     tri_is_triangular — isTriangular(tri(n)) = true for all n
                         (uses Nat.sqrt, even/odd, ring)

  3. Composition and chaining:
     tri_tri_is_triangular — tri(tri(n)) is always triangular
     tri_plus_succ_is_triangular — tri(n)+(n+1) is triangular
                                   (chains tri_succ + tri_is_triangular)

  4. Concrete applications (structural proofs, not native_decide):
     deep_tri_n3_triangular — 55 is triangular because 55 = tri(tri(4))
     deep_tri_n4_triangular — 666 is triangular because 666 = tri(tri(8))

  5. The XOR cycle theorem:
     ((((G₀ ⊕ G₁) ⊕ G₀) ⊕ G₁) ⊕ G₀) = G₀
     producing 5 states from 2 constants

  6. The bounded TriSum-Recast theorem:
     Recast values are triangular for n ∈ {2, 3, 4}
     Pattern breaks at n = 5

  7. Deep structure:
     Tri[Tri[4]] = 55 (n=3 case)
     Tri[Tri[8]] = 666 (n=4 case)

  Open for future work:
  - Full TriSum definition and closed-form proof
  - Why the pattern breaks at n=5
  - Connection to φ = (1 + √5)/2
-/
