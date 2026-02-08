/-
  BridgeB.lean — Scratch file for Approach B bridge proof
  Attempt to prove digitsToNat_arith_seq via Mathlib's ofDigits infrastructure.
  Move to private/baks/ after development.
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Indexes

-- Local definitions (same as TriSum.lean)
def digitsToNat' (b : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * b + d) 0

-- Already proved — reproduce for scratch testing
theorem digitsToNat_eq_ofDigits_reverse' (b : Nat) (L : List Nat) :
    digitsToNat' b L = Nat.ofDigits b L.reverse := by
  unfold digitsToNat'
  rw [Nat.ofDigits_eq_foldr]
  conv_lhs => rw [← List.reverse_reverse L]
  rw [List.foldl_reverse]
  congr 1
  ext d acc
  push_cast
  ring

-- === Approach B: Prove via ofDigits_cons induction on reversed list ===

-- Key insight: after converting digitsToNat to ofDigits via reverse,
-- we can use ofDigits_cons for the inductive step instead of
-- digitsToNat_append_single.

-- Step 1: reverse of mapped range decomposes as cons
theorem reverse_arith_seq_succ (c z : Nat) :
    ((List.range (z + 1)).map (· + c)).reverse =
    (c + z) :: ((List.range z).map (· + c)).reverse := by
  rw [List.range_succ, List.map_append, List.map_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      Nat.add_comm z c]

-- Step 2: The core Approach B bridge via ofDigits_cons
-- Prove: ofDigits b (reversed arith seq) = Finset.sum with little-endian powers
-- i.e., ofDigits b [c+z-1, ..., c+1, c] = Σ_{i<z} (c+i) * b^(z-1-i)
-- But ofDigits gives the LITTLE-endian interpretation:
-- ofDigits b [c+z-1, ..., c] = (c+z-1)*b^0 + (c+z-2)*b^1 + ... + c*b^(z-1)
-- = Σ_{i<z} (c+z-1-i) * b^i

-- So actually: digitsToNat b [c, c+1, ..., c+z-1]
-- = ofDigits b [c+z-1, ..., c+1, c]     (reverse)
-- = Σ_{i<z} (c+z-1-i) * b^i             (ofDigits little-endian)

-- And our target is: Σ_{i<z} (c+i) * b^(z-1-i)

-- These are the SAME sum under substitution j = z-1-i.
-- So the approach is:
-- 1. Prove ofDigits form = little-endian Finset.sum
-- 2. Re-index to big-endian Finset.sum

-- Step 2a: ofDigits of reversed arith seq = little-endian Finset.sum
theorem ofDigits_reversed_arith_seq (b c z : Nat) :
    Nat.ofDigits b ((List.range z).map (· + c)).reverse =
    (Finset.range z).sum (fun i => (c + z - 1 - i) * b ^ i) := by
  induction z with
  | zero => simp
  | succ n ih =>
    rw [reverse_arith_seq_succ, Nat.ofDigits_cons, ih, Finset.sum_range_succ, Finset.mul_sum]
    -- LHS: (c+n) + Σ_{i<n} b * ((c+n-1-i) * b^i)
    -- RHS: Σ_{i<n} (c+(n+1)-1-i) * b^i + (c+(n+1)-1-n) * b^n
    -- Strategy: show both sides = Σ_{j<n+1} (c+n-j)*b^j
    -- Simplify LHS sum terms: b * (x * b^i) = x * b^(i+1)
    have h1 : ∀ i ∈ Finset.range n,
        b * ((c + n - 1 - i) * b ^ i) = (c + n - 1 - i) * b ^ (i + 1) := by
      intro i _; rw [mul_left_comm, ← pow_succ']
    rw [Finset.sum_congr rfl h1]
    -- Simplify RHS Nat subtraction: c+(n+1)-1-i = c+n-i
    have h2 : ∀ i ∈ Finset.range n,
        (c + (n + 1) - 1 - i) * b ^ i = (c + n - i) * b ^ i := by
      intro i _; rfl  -- kernel normalizes c+(n+1)-1 to c+n
    have h3 : (c + (n + 1) - 1 - n) * b ^ n = (c + n - n) * b ^ n := by
      rfl  -- same defeq normalization
    rw [Finset.sum_congr rfl h2, h3, ← Finset.sum_range_succ]
    -- Both sides = Σ_{j<n+1} (c+n-j)*b^j, decomposed differently
    -- Expand RHS via sum_range_succ' to match LHS structure
    rw [Finset.sum_range_succ' (fun j => (c + n - j) * b ^ j)]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    -- Goal: (c+n) + Σ (c+n-1-i)*b^(i+1) = Σ (c+n-(i+1))*b^(i+1) + (c+n)
    rw [add_comm (c + n)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1; omega

-- Bounded checks
theorem ofDigits_check_1 :
    Nat.ofDigits 10 ((List.range 4).map (· + 0)).reverse = 123 := by native_decide
theorem ofDigits_check_2 :
    (Finset.range 4).sum (fun i => (0 + 4 - 1 - i) * 10 ^ i) = 123 := by native_decide
