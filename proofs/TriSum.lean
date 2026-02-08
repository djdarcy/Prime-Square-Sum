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
import Mathlib.Algebra.Ring.GeomSum
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

-- === Bridge lemma helpers (Approach A — kept for reference) ===

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

-- === Approach B infrastructure (ofDigits-based) ===

/-- Reverse of mapped range decomposes as cons (for ofDigits_cons induction). -/
theorem reverse_arith_seq_succ (c z : Nat) :
    ((List.range (z + 1)).map (· + c)).reverse =
    (c + z) :: ((List.range z).map (· + c)).reverse := by
  rw [List.range_succ, List.map_append, List.map_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      Nat.add_comm z c]

/-- ofDigits of reversed arithmetic sequence = little-endian Finset.sum.
    ofDigits b [c+z-1, ..., c] = Σ_{i<z} (c+z-1-i) * b^i -/
theorem ofDigits_reversed_arith_seq (b c z : Nat) :
    Nat.ofDigits b ((List.range z).map (· + c)).reverse =
    (Finset.range z).sum (fun i => (c + z - 1 - i) * b ^ i) := by
  induction z with
  | zero => simp
  | succ n ih =>
    rw [reverse_arith_seq_succ, Nat.ofDigits_cons, ih, Finset.sum_range_succ, Finset.mul_sum]
    have h1 : ∀ i ∈ Finset.range n,
        b * ((c + n - 1 - i) * b ^ i) = (c + n - 1 - i) * b ^ (i + 1) := by
      intro i _; rw [mul_left_comm, ← pow_succ']
    rw [Finset.sum_congr rfl h1]
    have h2 : ∀ i ∈ Finset.range n,
        (c + (n + 1) - 1 - i) * b ^ i = (c + n - i) * b ^ i := by
      intro i _; rfl
    have h3 : (c + (n + 1) - 1 - n) * b ^ n = (c + n - n) * b ^ n := by rfl
    rw [Finset.sum_congr rfl h2, h3, ← Finset.sum_range_succ]
    rw [Finset.sum_range_succ' (fun j => (c + n - j) * b ^ j)]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    rw [add_comm (c + n)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1; omega

-- === The core bridge lemma ===

/-- Core bridge: digitsToNat of an arithmetic sequence [c, c+1, ..., c+z-1]
    equals the positional-weight Finset.sum.
    Proof via Approach B: reverse → ofDigits → little-endian sum → re-index via sum_flip. -/
theorem digitsToNat_arith_seq (b c z : Nat) :
    digitsToNat b ((List.range z).map (· + c)) =
    (Finset.range z).sum (fun i => (c + i) * b ^ (z - 1 - i)) := by
  rw [digitsToNat_eq_ofDigits_reverse, ofDigits_reversed_arith_seq]
  -- Goal: Σ_{i<z} (c+z-1-i)*b^i = Σ_{i<z} (c+i)*b^(z-1-i)
  cases z with
  | zero => simp
  | succ n =>
    -- sum_flip: Σ_{r<n+1} f(n-r) = Σ_{k<n+1} f(k)
    -- Set f(k) = (c+k)*b^(n-k). Then f(n-r) = (c+n-r)*b^r = LHS term.
    rw [show (Finset.range (n + 1)).sum (fun i => (c + (n + 1) - 1 - i) * b ^ i) =
            (Finset.range (n + 1)).sum (fun r => (fun k => (c + k) * b ^ (n - k)) (n - r)) from by
      apply Finset.sum_congr rfl; intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 1
      · omega  -- c + n - i = c + (n - i)
      · congr 1; omega  -- b^i = b^(n-(n-i)), reduce to i = n-(n-i)
    ]
    rw [Finset.sum_flip (fun k => (c + k) * b ^ (n - k))]
    -- Σ (c+k)*b^(n-k) vs Σ (c+i)*b^(n+1-1-i): kernel normalizes n+1-1-i to n-i
    congr 1

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

-- === Phase 3C: Algebraic decomposition of rowValue' ===

/-- Decomposition: rowValue' splits into a constant-coefficient geometric sum
    plus a linearly-weighted power sum.
    rowValue'(b,z) = (b - tri z) * Σ b^(z-1-i) + Σ i * b^(z-1-i) -/
theorem rowValue'_split (b z : Nat) :
    rowValue' b z =
    (b - tri z) * (Finset.range z).sum (fun i => b ^ (z - 1 - i)) +
    (Finset.range z).sum (fun i => i * b ^ (z - 1 - i)) := by
  unfold rowValue'
  conv_lhs => arg 2; ext i; rw [Nat.add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.mul_sum]

-- Bounded verification of decomposition
theorem rowValue'_split_10_3 :
    rowValue' 10 3 =
    (10 - tri 3) * ((Finset.range 3).sum (fun i => 10 ^ (2 - i))) +
    (Finset.range 3).sum (fun i => i * 10 ^ (2 - i)) := by native_decide

theorem rowValue'_split_6_2 :
    rowValue' 6 2 =
    (6 - tri 2) * ((Finset.range 2).sum (fun i => 6 ^ (1 - i))) +
    (Finset.range 2).sum (fun i => i * 6 ^ (1 - i)) := by native_decide

-- === Phase 3C: Algebraic stf and bridge to stf' ===

/-- Convert List.foldl addition to Finset.sum: the standard bridge
    from algorithmic foldl accumulation to algebraic Finset.sum. -/
theorem list_foldl_add_eq_finset_sum (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = (Finset.range n).sum f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl]
    rw [ih]

/-- Algebraic stf: Finset.sum of rowValue' over all rows.
    Equivalent to stf but uses rowValue' for algebraic manipulation. -/
def stf' (b : Nat) : Nat :=
  (Finset.range (qg b)).sum (fun i => rowValue' b (i + 1))

/-- The algorithmic stf (foldl-based) equals the algebraic stf' (Finset.sum).
    Bridges the computable definition to a form amenable to algebraic proof. -/
theorem stf_eq_stf' (b : Nat) : stf b = stf' b := by
  unfold stf stf'
  rw [list_foldl_add_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact rowValue_eq_rowValue' b (i + 1)

-- Bounded verification: stf = stf' for known bases
theorem stf_eq_stf'_6 : stf 6 = stf' 6 := by native_decide
theorem stf_eq_stf'_10 : stf 10 = stf' 10 := by native_decide
theorem stf_eq_stf'_15 : stf 15 = stf' 15 := by native_decide

-- === Phase 3C: Recursive relation helpers ===

/-- Geometric sum identity: b * Σ_{i<n} b^i + 1 = Σ_{i<n+1} b^i.
    Division-free form of the standard geometric series recursion. -/
theorem geom_sum_mul_add_one (b n : Nat) :
    b * (Finset.range n).sum (fun i => b ^ i) + 1 =
    (Finset.range (n + 1)).sum (fun i => b ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.mul_add,
        ← pow_succ', add_right_comm, ih]

-- Bounded verification of geometric identity
theorem geom_sum_mul_add_one_10_3 :
    10 * (1 + 10 + 100) + 1 = 1 + 10 + 100 + 1000 := by norm_num

/-- Power sum reindexing: descending powers equal ascending powers.
    Σ_{i<z} b^(z-1-i) = Σ_{i<z} b^i via sum_flip. -/
theorem power_sum_reverse (b z : Nat) :
    (Finset.range z).sum (fun i => b ^ (z - 1 - i)) =
    (Finset.range z).sum (fun i => b ^ i) := by
  cases z with
  | zero => simp
  | succ n =>
    rw [show (Finset.range (n + 1)).sum (fun i => b ^ (n + 1 - 1 - i)) =
            (Finset.range (n + 1)).sum (fun r => (fun k => b ^ k) (n - r)) from by
      apply Finset.sum_congr rfl; intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 1]
    exact Finset.sum_flip (fun k => b ^ k)

-- === Phase 3C: Recursive relation for rowValue' ===

/-- Recursive relation (additive form): rowValue'(b, z+1) relates to b * rowValue'(b, z)
    with a geometric sum correction term. The additive form avoids Nat subtraction underflow.
    Hypothesis: tri(z+1) ≤ b ensures all digit values are non-negative. -/
theorem rowValue'_succ_add (b z : Nat) (h : tri (z + 1) ≤ b) :
    rowValue' b (z + 1) + (z + 1) * (Finset.range (z + 1)).sum (fun i => b ^ i) =
    b * rowValue' b z + (b - tri z + z) := by
  simp only [rowValue']
  -- Step 1: Peel last term from LHS sum
  rw [Finset.sum_range_succ]
  -- Note: b^(z+1-1-z) is kernel-defeq to b^0 = 1, so no simp needed
  -- Step 2: Factor b from remaining z terms
  have hfact : ∀ i ∈ Finset.range z,
      (b - tri (z + 1) + i) * b ^ (z + 1 - 1 - i) =
      b * ((b - tri (z + 1) + i) * b ^ (z - 1 - i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show z + 1 - 1 - i = (z - 1 - i) + 1 from by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hfact, ← Finset.mul_sum]
  -- Step 3: Decompose RHS sum coefficients: (b-tri z+i) = (b-tri(z+1)+i) + (z+1)
  have hcoeff : ∀ i, b - tri z + i = (b - tri (z + 1) + i) + (z + 1) := by
    intro i; have := tri_succ z; omega
  have hdecomp : (Finset.range z).sum (fun i => (b - tri z + i) * b ^ (z - 1 - i)) =
      (Finset.range z).sum (fun i => (b - tri (z + 1) + i) * b ^ (z - 1 - i)) +
      (z + 1) * (Finset.range z).sum (fun i => b ^ (z - 1 - i)) := by
    simp_rw [hcoeff, Nat.add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdecomp, Nat.mul_add]
  -- Step 4: Both sides have b * Σ(c+i)*b^k as prefix. Align associativity and cancel.
  rw [add_assoc, add_assoc]
  congr 1
  -- Goal: (b-tri(z+1)+z)*b^(z+1-1-z) + (z+1)*Σ_{i<z+1} b^i
  --     = b*((z+1)*Σ_{i<z} b^(z-1-i)) + (b-tri z+z)
  -- Step 5: Rewrite descending powers to ascending
  rw [power_sum_reverse b z]
  -- Step 6: Replace Σ_{i<z+1} b^i with b*Σ_{i<z} b^i + 1
  rw [← geom_sum_mul_add_one b z]
  -- Step 7: Distribute and commute
  rw [Nat.mul_add, Nat.mul_one, mul_left_comm (z + 1) b]
  -- Normalize the last-term power: b^(z+1-1-z) = b^0 = 1
  rw [show z + 1 - 1 - z = 0 from by omega, pow_zero, mul_one]
  -- Goal: (b-tri(z+1)+z) + (b*((z+1)*Σ) + (z+1)) = b*((z+1)*Σ) + (b-tri z+z)
  -- Cancel b*((z+1)*Σ) from both sides
  rw [← add_assoc, add_comm (b - tri (z + 1) + z), add_assoc]
  congr 1
  -- Goal: (b-tri(z+1)+z) + (z+1) = (b-tri z+z)
  have := tri_succ z
  omega

-- Bounded verification of recursive relation
theorem rowValue'_succ_add_10_2 :
    rowValue' 10 3 + 3 * (1 + 10 + 100) =
    10 * rowValue' 10 2 + (10 - tri 2 + 2) := by native_decide

theorem rowValue'_succ_add_6_1 :
    rowValue' 6 2 + 2 * (1 + 6) =
    6 * rowValue' 6 1 + (6 - tri 1 + 1) := by native_decide

-- === Phase 3C/3D: Geometric sum closed-form connection ===

/-- Connect descending power sums to Mathlib's geometric series closed form.
    Σ_{i<z} b^(z-1-i) = (b^z - 1) / (b - 1) for b ≥ 2.
    Combines power_sum_reverse with Nat.geomSum_eq. -/
theorem power_sum_closed (b z : Nat) (hb : 2 ≤ b) :
    (Finset.range z).sum (fun i => b ^ (z - 1 - i)) =
    (b ^ z - 1) / (b - 1) := by
  rw [power_sum_reverse]
  exact Nat.geomSum_eq hb z

-- Bounded verification of closed-form connection
theorem power_sum_closed_10_3 :
    (Finset.range 3).sum (fun i => 10 ^ (2 - i)) = (1000 - 1) / 9 := by native_decide

theorem power_sum_closed_6_4 :
    (Finset.range 4).sum (fun i => 6 ^ (3 - i)) = (1296 - 1) / 5 := by native_decide

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
