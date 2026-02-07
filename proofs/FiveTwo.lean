/-
  FiveTwo.lean — The 5-and-2 Pattern (XOR Cycle)
  ================================================

  Formalizes the 5-state XOR cycle from
  "Zero_AG to The Scarcity Framework: A Guide" by D. Darcy

  The cycle: G₀ → E → G₁ → F → G₀
  - 2 generating constants (G₀ = biconditional, G₁ = XOR)
  - 5 positions in the cycle
  - 4 distinct states visited
  - 10 = 2 × 5 (base-10 emerges from the pattern)
-/

-- No Mathlib imports needed — pure Boolean logic

-- ============================================================
-- PART 1: Logic State Representation
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
-- PART 2: The 5-State Cycle
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
-- PART 3: The 5-and-2 Pattern
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
