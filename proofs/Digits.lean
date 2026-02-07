/-
  Digits.lean — Digit Representation and Meta-Properties
  ======================================================

  General-purpose digit operations built on Mathlib's Nat.digits/Nat.ofDigits.
  These are base-independent tools for working with digit representations.

  Structure:
  1. Recast — reinterpret digits from one base to another
  2. Digit meta-properties — digitSum, digitCount, digitalRoot
  3. Casting-out theorem — digit sum mod (b-1) equivalence
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Div

-- ============================================================
-- PART 1: Recast
-- ============================================================

/-
  Recast formalizes the Mathematica function:

    Recast[x_, sourceBase_, targetBase_, digitList_:Automatic] :=
      Module[{list, str, newValue = 0},
        list = If[digitList === Automatic,
          If[sourceBase <= 36,
            CharacterRange["0","9"] ~Join~ CharacterRange["A","Z"],
            Message[Recast::nolist]; Return[$Failed]],
          digitList];
        str = If[digitList === Automatic,
          IntegerString[x, sourceBase],
          CustomIntegerString[x, sourceBase, list]];
        newValue = CustomFromDigits[str, targetBase, list];
        newValue]

  The Mathematica version routes through string representation because it
  supports custom digit alphabets for arbitrary bases. For example, a
  666-symbol alphabet for base-666 number representation:

    digitList666 = Join[
      CharacterRange["0","9"],         -- 10 digits
      CharacterRange["a","z"],         -- 26 Latin lowercase
      CharacterRange["A","Z"],         -- 26 Latin uppercase
      {α..ω},                          -- 25 Greek lowercase
      {Hebrew letters},                -- 22 characters
      {Cyrillic lower/upper},          -- 64 characters
      {Hiragana}, {Katakana},          -- 166 characters
      {CJK Han subset},               -- 201 characters
      {Latin Extended}, {Α..Ω}]        -- 127 characters
    Length[digitList666] = 666          -- "0" to "Ω"

  Our Lean definition captures the mathematical core directly:
  Nat.digits extracts digit values via repeated mod/quotient,
  Nat.ofDigits reconstructs via positional weighting (Horner's method).
  Both are little-endian, so the composition needs no list reversal.
  The character-mapping layer is unnecessary since we work with
  numeric digit values (0..base-1) rather than string symbols.

  This handles all bases uniformly — including base 666 — without
  requiring any alphabet or display infrastructure.
-/

/-- Recast: reinterpret the digits of x in source_base as a number in target_base.
    e.g., recast 6 10 35 = 55 (digits of 35 in base 6 are [5,5], read as 55 in base 10) -/
def recast (source_base target_base x : Nat) : Nat :=
  Nat.ofDigits target_base (Nat.digits source_base x)

-- Basic recast verification
#eval recast 6 10 35    -- 55
#eval recast 3 10 3     -- 10
#eval recast 10 10 666  -- 666

/-- Round-trip: recasting in the same base is the identity.
    Follows directly from Nat.ofDigits_digits. -/
theorem recast_self (b x : Nat) : recast b b x = x := by
  unfold recast
  exact Nat.ofDigits_digits b x

-- ============================================================
-- PART 2: Digit Meta-Properties
-- ============================================================

/-
  The digit *representation* of a number carries structural information
  beyond its numeric value. Different bases reveal different patterns:

  - digitSum: sum of digits (connected to divisibility via casting out)
  - digitCount: number of digits (compression — 665 is 3 digits in base 10
    but 1 digit in base 666)
  - digitalRoot: iterated digit sum to a single "digit"

  These connect to Mathlib's general casting-out theorem:
    Nat.modEq_digits_sum : b' % b = 1 → n ≡ (digits b' n).sum [MOD b]

  For base 10: 10 % 9 = 1, so n ≡ digitSum(10, n) mod 9 (casting out nines)
  For base 666: 666 % 665 = 1, so n ≡ digitSum(666, n) mod 665

  This means digit sums in different bases reveal different divisibility
  structures — the same number has different "fingerprints" depending on
  how you represent it.
-/

/-- Sum of digits of n in base b.
    e.g., digitSum 10 666 = 6 + 6 + 6 = 18 -/
def digitSum (b n : Nat) : Nat := (Nat.digits b n).sum

/-- Number of digits of n in base b.
    e.g., digitCount 10 665 = 3, but digitCount 666 665 = 1 -/
def digitCount (b n : Nat) : Nat := (Nat.digits b n).length

/-- Digital root: the single-digit residue obtained by iterating digit sum.
    For b ≥ 2 and n > 0, this equals 1 + ((n - 1) % (b - 1)).

    Matches the Python implementation:
      def digital_root(n): return 0 if n == 0 else 1 + ((n - 1) % 9)
    generalized to arbitrary bases.

    The formula works because n ≡ digitSum(b, n) mod (b-1), so repeated
    application converges to n mod (b-1), adjusted to the range [1, b-1]
    instead of [0, b-2]. -/
def digitalRoot (b n : Nat) : Nat :=
  if b ≤ 1 ∨ n = 0 then n
  else 1 + ((n - 1) % (b - 1))

-- Basic digit meta verification
#eval digitSum 10 666      -- 18
#eval digitCount 10 666    -- 3
#eval digitalRoot 10 666   -- 9

-- The compression point: same number, different digit structure
#eval digitCount 10 665    -- 3 digits in base 10
#eval digitCount 666 665   -- 1 digit in base 666

-- Concrete digit meta-properties of key values
theorem digitSum_666 : digitSum 10 666 = 18 := by native_decide
theorem digitCount_666 : digitCount 10 666 = 3 := by native_decide
theorem digitalRoot_666 : digitalRoot 10 666 = 9 := by native_decide

-- The digital root detects divisibility by 9
theorem six_six_six_div_nine : 9 ∣ 666 := by omega

-- Base changes alter digit structure (the alphabet encodes information)
theorem digitCount_665_base10 : digitCount 10 665 = 3 := by native_decide
theorem digitCount_665_base666 : digitCount 666 665 = 1 := by native_decide

-- Digit sums in different bases reveal different divisibility
theorem digitSum_665_base10 : digitSum 10 665 = 17 := by native_decide
theorem digitSum_665_base666 : digitSum 666 665 = 665 := by native_decide

-- ============================================================
-- PART 3: Casting-Out Theorem
-- ============================================================

/-- Casting out (b-1): n is congruent to its base-b digit sum modulo (b-1).
    This restates Mathlib's `Nat.modEq_digits_sum` using our `digitSum` naming.
    For base 10: n ≡ digitSum(10, n) mod 9.
    For base 666: n ≡ digitSum(666, n) mod 665. -/
theorem digitSum_mod (b n : Nat) (hb : b % (b - 1) = 1) :
    n ≡ digitSum b n [MOD (b - 1)] := by
  unfold digitSum
  exact Nat.modEq_digits_sum (b - 1) b hb n

-- Verify the casting-out precondition for key bases
-- (b % (b-1) = 1 holds for all b ≥ 2)
theorem cast_out_base10 : 10 % 9 = 1 := by native_decide
theorem cast_out_base666 : 666 % 665 = 1 := by native_decide
