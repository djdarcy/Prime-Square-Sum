/-
  TriSum.lean — Triangular Numbers and the stf Function
  ======================================================

  Basic Lean 4 formalizations for concepts from
  "Zero_AG to The Scarcity Framework: A Guide" by D. Darcy

  Formalizations for the triangular number system and its
  digit-arrangement sum function (stf/trisum).

  Structure:
  1. Triangular number definitions and properties (tri, isTriangular)
  2. Recursive and inductive proofs (tri_succ, two_mul_tri)
  3. Triangular recognition correctness (tri_is_triangular)
  4. stf: sum of triangular digit rows (digitsToNat, qg, rowValue, stf)
  4b. Algebraic rowValue and bridge lemma (rowValue' ↔ rowValue via Finset.sum)
  5. Bounded recast pattern (uses recast from Digits.lean)
  6. Deep triangular structure
  7. Synthesis — composition theorems
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Digits.Lemmas
import Digits

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

-- ============================================================
-- PART 2: Recursive & Inductive Properties
-- ============================================================

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
-- PART 3: Checking if a number is triangular
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
-- PART 4: The stf Function (Sum of Triangular Digit Rows)
-- ============================================================

/-- Interpret a list of digits as a base-b number (big-endian).
    e.g., digitsToNat 10 [4, 5, 6] = 456 -/
def digitsToNat (b : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * b + d) 0

/-- Inverse triangular: find r such that tri(r) = b.
    For triangular b, returns the unique r with r*(r+1)/2 = b. -/
def qg (b : Nat) : Nat :=
  (Nat.sqrt (1 + 8 * b) - 1) / 2

/-- Row z from top: z consecutive digits starting at (b - tri(z)).
    For base 10: row 1 = [9], row 2 = [7,8], row 3 = [4,5,6], row 4 = [0,1,2,3] -/
def rowValue (b z : Nat) : Nat :=
  let start := b - tri z
  digitsToNat b ((List.range z).map (· + start))

/-- stf(b): sum of all triangular row values for base b.
    Arranges digits 0..b-1 into a triangle of qg(b) rows and sums the
    base-b interpretation of each row. -/
def stf (b : Nat) : Nat :=
  let r := qg b
  (List.range r).foldl (fun acc i => acc + rowValue b (i + 1)) 0

-- qg correctness on known triangular numbers
theorem qg_three : qg 3 = 2 := by native_decide
theorem qg_six : qg 6 = 3 := by native_decide
theorem qg_ten : qg 10 = 4 := by native_decide

-- Individual row values for base 10
theorem row1_base10 : rowValue 10 1 = 9 := by native_decide
theorem row2_base10 : rowValue 10 2 = 78 := by native_decide
theorem row3_base10 : rowValue 10 3 = 456 := by native_decide
theorem row4_base10 : rowValue 10 4 = 123 := by native_decide

-- The core computation: stf(10) = 666
theorem stf_ten : stf 10 = 666 := by native_decide

-- ============================================================
-- PART 4b: Algebraic rowValue and Bridge Lemma
-- ============================================================

-- The algebraic form expresses rowValue as a positional-weight sum:
--   rowValue'(b, z) = Σ_{i=0}^{z-1} (b - tri(z) + i) * b^(z-1-i)
-- This is equivalent to the algorithmic foldl definition (rowValue).
-- The bridge lemma proves this equivalence generally by induction.

/-- Algebraic rowValue: closed-form Finset.sum with positional powers.
    Equivalent to rowValue but amenable to algebraic manipulation. -/
def rowValue' (b z : Nat) : Nat :=
  (Finset.range z).sum (fun i => (b - tri z + i) * b ^ (z - 1 - i))

-- Verify algebraic rowValue matches algorithmic for base 10
#eval rowValue' 10 1  -- 9
#eval rowValue' 10 2  -- 78
#eval rowValue' 10 3  -- 456
#eval rowValue' 10 4  -- 123

-- === Mathlib connection: digitsToNat = ofDigits via reverse ===

/-- Our big-endian foldl equals Mathlib's little-endian ofDigits on the reversed list. -/
theorem digitsToNat_eq_ofDigits_reverse (b : Nat) (L : List Nat) :
    digitsToNat b L = Nat.ofDigits b L.reverse := by
  unfold digitsToNat
  rw [Nat.ofDigits_eq_foldr]
  conv_lhs => rw [← List.reverse_reverse L]
  rw [List.foldl_reverse]
  congr 1
  ext d acc
  push_cast
  ring

-- === Bridge lemma helpers ===

/-- foldl over appended singleton: digitsToNat of L++[d] = digitsToNat(L)*b + d -/
theorem digitsToNat_append_single (b : Nat) (L : List Nat) (d : Nat) :
    digitsToNat b (L ++ [d]) = digitsToNat b L * b + d := by
  unfold digitsToNat
  rw [List.foldl_append]
  simp [List.foldl]

/-- List.range (z+1) mapped = List.range z mapped ++ [c + z] -/
theorem range_map_succ (c z : Nat) :
    (List.range (z + 1)).map (· + c) = (List.range z).map (· + c) ++ [c + z] := by
  rw [List.range_succ, List.map_append, List.map_singleton, Nat.add_comm z c]

-- === The core bridge lemma ===

/-- Core bridge: digitsToNat of an arithmetic sequence [c, c+1, ..., c+z-1]
    equals the positional-weight Finset.sum.
    Proved by induction on z, using foldl append and power properties. -/
theorem digitsToNat_arith_seq (b c z : Nat) :
    digitsToNat b ((List.range z).map (· + c)) =
    (Finset.range z).sum (fun i => (c + i) * b ^ (z - 1 - i)) := by
  induction z with
  | zero =>
    simp [digitsToNat, List.range_zero, List.map_nil]
  | succ n ih =>
    rw [range_map_succ, digitsToNat_append_single]
    rw [Finset.sum_range_succ]
    have hn : n + 1 - 1 - n = 0 := by omega
    rw [hn, pow_zero, mul_one]
    -- n+1-1-x is defeq to n-x, so the sum exponents simplify automatically
    congr 1
    rw [ih, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [mul_assoc, ← pow_succ]
    congr 1  -- (c+i) = (c+i), reduces to b^(n-1-i+1) = b^(n+1-1-i)
    congr 1  -- reduces to n-1-i+1 = n+1-1-i
    omega

-- === General bridge: rowValue = rowValue' ===

/-- The algorithmic rowValue (foldl-based) equals the algebraic rowValue' (Finset.sum).
    This bridges the computable definition to a form amenable to algebraic proof. -/
theorem rowValue_eq_rowValue' (b z : Nat) :
    rowValue b z = rowValue' b z := by
  unfold rowValue rowValue'
  exact digitsToNat_arith_seq b (b - tri z) z

-- Bounded verification: rowValue = rowValue' for specific bases
theorem rv_eq_rv'_10_1 : rowValue 10 1 = rowValue' 10 1 := by native_decide
theorem rv_eq_rv'_10_2 : rowValue 10 2 = rowValue' 10 2 := by native_decide
theorem rv_eq_rv'_10_3 : rowValue 10 3 = rowValue' 10 3 := by native_decide
theorem rv_eq_rv'_10_4 : rowValue 10 4 = rowValue' 10 4 := by native_decide
theorem rv_eq_rv'_6_1 : rowValue 6 1 = rowValue' 6 1 := by native_decide
theorem rv_eq_rv'_6_2 : rowValue 6 2 = rowValue' 6 2 := by native_decide
theorem rv_eq_rv'_6_3 : rowValue 6 3 = rowValue' 6 3 := by native_decide
theorem rv_eq_rv'_15_1 : rowValue 15 1 = rowValue' 15 1 := by native_decide
theorem rv_eq_rv'_15_5 : rowValue 15 5 = rowValue' 15 5 := by native_decide

-- ============================================================
-- PART 5: Bounded Recast Pattern
-- ============================================================

-- recast, digitSum, digitCount, digitalRoot are defined in Digits.lean.
-- This section applies recast to stf/tri — combining digit operations
-- with the triangular number system.

/--
  THEOREM (Bounded): For n ∈ {2, 3, 4}, the recast of stf(tri(n))
  from base tri(n) to base 10 yields triangular numbers.
  The pattern breaks at n=5.
-/

-- n=2: base=3,  stf=3,     recast=10   = tri(4)   OK
-- n=3: base=6,  stf=35,    recast=55   = tri(10)  OK
-- n=4: base=10, stf=666,   recast=666  = tri(36)  OK
-- n=5: base=15, stf=24605, recast=7455 = NOT triangular

-- Concrete recast computations
theorem recast_stf_n2 : recast (tri 2) 10 (stf (tri 2)) = 10 := by native_decide
theorem recast_stf_n3 : recast (tri 3) 10 (stf (tri 3)) = 55 := by native_decide
theorem recast_stf_n4 : recast (tri 4) 10 (stf (tri 4)) = 666 := by native_decide
theorem recast_stf_n5 : recast (tri 5) 10 (stf (tri 5)) = 7455 := by native_decide

-- Triangularity of recast values
theorem recast_n2_triangular : isTriangular (recast (tri 2) 10 (stf (tri 2))) = true := by
  native_decide
theorem recast_n3_triangular : isTriangular (recast (tri 3) 10 (stf (tri 3))) = true := by
  native_decide
theorem recast_n4_triangular : isTriangular (recast (tri 4) 10 (stf (tri 4))) = true := by
  native_decide
theorem recast_n5_NOT_triangular : isTriangular (recast (tri 5) 10 (stf (tri 5))) = false := by
  native_decide

-- COROLLARY: The pattern breaks at n=5, suggesting base-10 (= tri(4))
-- is a structural boundary.

-- ============================================================
-- PART 6: Deep Triangular Structure
-- ============================================================
/-- For n=3: Recast = 55 = tri(10) = tri(tri(4)) -/
theorem deep_structure_n3 : tri (tri 4) = 55 := by native_decide

/-- For n=4: Recast = 666 = tri(36) = tri(tri(8)) -/
theorem deep_structure_n4 : tri (tri 8) = 666 := by native_decide

-- Observation: The index doubles from 4 to 8 as we go from n=3 to n=4.
-- At n=3: index = 4 = n + 1
-- At n=4: index = 8 = 2n
-- This transition occurs exactly at base-10.

-- ============================================================
-- PART 7: Synthesis — How the Pieces Fit Together
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

  5. The XOR cycle theorem (see FiveTwo.lean):
     ((((G₀ ⊕ G₁) ⊕ G₀) ⊕ G₁) ⊕ G₀) = G₀
     producing 5 states from 2 constants

  6. Digit operations (see Digits.lean):
     recast — reinterpret digits from one base to another
     recast_self — round-trip identity
     digitSum, digitCount, digitalRoot — digit meta-properties
     digitSum_mod — general casting-out theorem

  7. Bounded TriSum-Recast theorem (combines recast with stf/tri):
     recast_stf_n{2,3,4,5} — concrete recast computations
     Recast values are triangular for n ∈ {2, 3, 4}
     Pattern breaks at n = 5

  8. Deep structure:
     Tri[Tri[4]] = 55 (n=3 case)
     Tri[Tri[8]] = 666 (n=4 case)

  9. Algebraic bridge (Phase 3B):
     rowValue' — algebraic Finset.sum form of rowValue
     digitsToNat_eq_ofDigits_reverse — connects to Mathlib's ofDigits
     digitsToNat_arith_seq — core bridge: foldl arithmetic seq = Finset.sum
     rowValue_eq_rowValue' — general equivalence (no sorry!)
     Bounded verification for bases 6, 10, 15

  Open for future work:
  - Recursive relation: rowValue'(b, z+1) from rowValue'(b, z)
  - Closed-form Q(b,z) polynomial and equivalence with rowValue
  - Why the recast pattern breaks at n=5
  - Connection to φ = (1 + √5)/2
-/
