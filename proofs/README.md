# Formal Proofs

This folder contains formal mathematical proofs related to the Prime-Square-Sum conjecture and its connection to triangular number theory.

## Files

### TriSum.lean
Triangular number theory and the stf (trisum) function.

**Key theorems proven:**

*Foundations:*
- `tri_zero`, `tri_one`, `tri_four`, `tri_thirtysix` — Basic triangular number identities
- `tri_succ` — Recursive property: tri(n+1) = tri(n) + (n+1)
- `two_mul_tri` — Division-free formula: 2·tri(n) = n·(n+1), proved by induction on tri_zero + tri_succ

*Correctness bridge:*
- `tri_is_triangular` — For all n, isTriangular(tri(n)) = true. Proves the discriminant 1+8·tri(n) = (2n+1)² is always a perfect square.

*The stf function (sum of triangular digit rows):*
- `digitsToNat` — Interpret a digit list as a base-b number (big-endian)
- `qg` — Inverse triangular number
- `rowValue` — Value of row z in the triangular digit arrangement
- `stf` — Sum of all triangular row values for base b
- `stf_ten` — **stf(10) = 666** (via `native_decide`)
- `qg_ten`, `row1_base10`..`row4_base10` — Concrete verifications

*Composition and chaining (synthesis):*
- `tri_tri_is_triangular` — tri(tri(n)) is always triangular (composition)
- `tri_plus_succ_is_triangular` — tri(n)+(n+1) is triangular (chains tri_succ + tri_is_triangular)
- `deep_tri_n3_triangular` — 55 is triangular because 55 = tri(tri(4)), proved structurally
- `deep_tri_n4_triangular` — 666 is triangular because 666 = tri(tri(8)), proved structurally

*Algebraic rowValue and bridge lemma (Part 4b):*
- `rowValue'` — Algebraic Finset.sum definition with positional powers
- `digitsToNat_arith_seq` — Core bridge: foldl over arithmetic sequence equals Finset.sum with positional weights
- `rowValue_eq_rowValue'` — General equivalence between algorithmic and algebraic rowValue

*Phase 3C — Algebraic decomposition and recursive relation:*
- `rowValue'_split` — Decompose rowValue' into constant-coefficient geometric sum plus linearly-weighted power sum
- `stf'` / `stf_eq_stf'` — Bridge algorithmic stf (List.foldl) to algebraic stf' (Finset.sum)
- `geom_sum_mul_add_one` — Division-free geometric series recursion: b * Σ b^i + 1 = Σ b^i over extended range
- `power_sum_reverse` — Descending powers equal ascending powers via sum_flip
- `rowValue'_succ_add` — Recursive relation: rowValue'(b, z+1) in terms of b * rowValue'(b, z) with geometric sum correction (additive form, avoids Nat subtraction underflow)
- `power_sum_closed` — Closed form via Mathlib's `Nat.geomSum_eq`: Σ b^(z-1-i) = (b^z - 1)/(b - 1) for b ≥ 2

*Phase 3D — Telescoping stf':*
- `rowValue'_zero`, `rowValue'_one` — Boundary lemmas: rv'(b,0) = 0, rv'(b,1) = b-1
- `sum_rowValue'_succ_eq` — Element-wise summed recursive relation over Finset.range
- `rowValue'_sum_index_shift` — Index shift: Σ_{z<r} rv'(b,z) + rv'(b,r) = stf'(b), bridging 0-indexed sum with 1-indexed stf' via `sum_range_succ` + `sum_range_succ'`
- `stf'_telescope` — **Main telescoping theorem**: stf'(b) + C + b·rv'(b,r) = b·stf'(b) + B, where C = Σ(z+1)·G(z+1) (correction), B = Σ(b-tri(z)+z) (boundary), r = qg(b). Additive form avoids all Nat subtraction underflow. Reduces stf to three simpler quantities.

*Step 4A — Boundary sum closed form:*
- `six_mul_tri` — Helper: 6 * tri(n) = 3 * n * (n + 1)
- `six_mul_sum_tri` — Tetrahedral identity: 6 * Σ_{z<r} tri(z) = (r-1)*r*(r+1)
- `boundary_step` (private) — Induction step: 6*(b - tri(n) + n) + 3*n*(n-1) = 6*b
- `boundary_sum_closed` — **Boundary sum B closed form**: 6 * Σ_{z<r}(b - tri(z) + z) + r*(r-1)*(r-2) = 6*r*b. Nat-safe additive identity giving a closed form for the boundary sum B from the telescoping theorem. Uses cubic decomposition via `ring` and omega over opaque nonlinear atoms.

*Step 4B — Arithmetic-geometric sum identity:*
- `arith_geom_sum` — **Arithmetic-geometric sum closed form**: (b-1)² · Σ_{i<n} i·bⁱ + n·bⁿ = (n-1)·b^(n+1) + b. The mathematical bottleneck for the stf closed form — steps 4C, 4D, and 4F all depend on this identity. Proved by `cases b` (Nat (b-1)²=0 pitfall when b=0), then induction on n with `ring`-provable step lemma, `simp only [Nat.succ_sub_one]` normalization, and `omega` linear combination. No hypothesis on b needed.

*Step 4C — Correction sum C closed form:*
- `geom_sum_pred_mul_add_one` — Geometric sum with (b-1) factor: (b-1) * Σ_{i<n} b^i + 1 = b^n. Nat-safe additive form of (b-1)·G(n) = b^n - 1. Proved by `cases b` + induction with `add_right_comm` + `pow_succ` + `ring`. Requires `hb : 1 ≤ b`.
- `correction_sum_intermediate` — Intermediate identity: (b-1)·C + tri(r) = Σ_{j<r+1} j·b^j. Connects the correction sum C = Σ_{z<r}(z+1)·G(z+1) to the arithmetic-geometric sum. Proved by induction on r using explicit `have` bindings for `sum_range_succ` disambiguation, `mul_left_comm` for coefficient extraction, and `ring` for factoring with opaque Finset.sum variables.
- `correction_sum_closed` — **Correction sum C closed form**: (b-1)² · ((b-1)·C + tri(r)) + (r+1)·b^(r+1) = r·b^(r+2) + b. Nat-safe additive identity combining `correction_sum_intermediate` with `arith_geom_sum`. Two-line proof via rewrite + exact.

*Step 4D — Last row rv' closed form (weighted power sum):*
- `weighted_sum_split` — Weighted sum decomposition: Σ_{i<r}(r-1-i)·b^i + Σ_{i<r} i·b^i = (r-1)·Σ_{i<r} b^i. Each summand satisfies (r-1-i) + i = r-1 for i < r. Via `sum_add_distrib` + `sum_congr` + `omega`.
- `weighted_sum_closed` — **Last row closed form**: (b-1)² · Σ_{i<r}(r-1-i)·b^i + (r-1)·(b-1) + b = b^r. Nat-safe additive identity for the weighted power sum appearing in the last row of the triangular digit arrangement. 4-step chain: multiply `weighted_sum_split` by (b-1)², factor via `geom_sum_pred_mul_add_one`, algebraic step via `cases b` + `cases r` + `pow_succ` + `ring`, then `omega` combines all hypotheses. Holds for all b ≥ 1, r ≥ 1.

*Step 4E — Per-row closed form (rowValue' assembly):*
- `weighted_power_sum_reverse` — Weighted power sum flip: Σ_{i<z} i·b^(z-1-i) = Σ_{i<z} (z-1-i)·b^i. Follows `power_sum_reverse` pattern via `sum_congr` + `omega` + `sum_flip`. No hypotheses needed.
- `rowValue'_closed_form` — **Per-row closed form**: (b-1)² · rv'(b,z) + (b-tri z)·(b-1) + (z-1)·(b-1) + b = (b-tri z)·(b-1)·b^z + b^z. Direct assembly from existing building blocks: `rowValue'_split` decomposes, `power_sum_reverse` + `weighted_power_sum_reverse` flip to ascending, `geom_sum_pred_mul_add_one` + `weighted_sum_closed` provide closed forms, `ring` pre-factors opaque atoms, `omega` closes. No induction or ℤ-casting needed. Requires `hb : 2 ≤ b`, `hz : 1 ≤ z`.

*Bounded verification:*
- TriSum-Recast theorem verification for n ∈ {2, 3, 4}; pattern breaks at n = 5
- `native_decide` verifications for rowValue' equivalence, decomposition, stf bridge, recursive relation, index shift, and telescoping across bases 6, 10, 15

*Dependency chain:*
```
tri_zero (base case) → tri_succ (recursion) → two_mul_tri (induction)
    → tri_is_triangular (correctness) → tri_tri_is_triangular (composition)
    → deep_tri_n3_triangular (55) + deep_tri_n4_triangular (666)

rowValue → rowValue_eq_rowValue' → rowValue'
    → rowValue'_split (decomposition)
    → stf_eq_stf' (algebraic stf bridge)
    → rowValue'_succ_add (recursive relation)
        ← geom_sum_mul_add_one + power_sum_reverse (helpers)
    → power_sum_closed (closed form via Nat.geomSum_eq)
    → sum_rowValue'_succ_eq (summed relation)
        → rowValue'_sum_index_shift (index shift)
        → stf'_telescope (telescoping identity)

two_mul_tri → six_mul_tri → six_mul_sum_tri (tetrahedral)
six_mul_tri → boundary_step → boundary_sum_closed (boundary sum B)

arith_geom_sum (arithmetic-geometric sum, Step 4B bottleneck)
    → correction_sum_intermediate (Step 4C, via geom_sum_pred_mul_add_one)
        → correction_sum_closed (Step 4C, combines with arith_geom_sum)
    → weighted_sum_split + weighted_sum_closed (Step 4D, also uses geom_sum_pred_mul_add_one)

rowValue'_split + power_sum_reverse + weighted_power_sum_reverse
    + geom_sum_pred_mul_add_one + weighted_sum_closed
    → rowValue'_closed_form (Step 4E, direct assembly)
    → [future] full stf = F(b) (Step 4F, combines 4A + 4B + 4C + 4D via telescoping)
```

*Critical path to stf(b) = F(b) closed form:*

The theorems below are on the direct path to proving `F(primesum(k₁,p₁)) = primesum(k₂,p₂)` — the constraint equation connecting triangular structure to prime structure.

| Role | Theorems |
|------|----------|
| **Foundation** | `tri_zero`, `tri_succ`, `two_mul_tri` |
| **Bridge** | `rowValue_eq_rowValue'` (algorithmic → algebraic) |
| **Algebraic stf** | `stf_eq_stf'`, `stf'_telescope` |
| **Closed forms** | `boundary_sum_closed` (4A), `arith_geom_sum` (4B), `correction_sum_closed` (4C), `weighted_sum_closed` (4D), `rowValue'_closed_form` (4E) |
| **Assembly** | [Step 4F — combines 4A + 4B + 4C + 4D + 4E via telescoping] |

Supporting theorems (used by the critical path but not on it directly): `six_mul_tri`, `boundary_step`, `geom_sum_pred_mul_add_one`, `weighted_sum_split`, `weighted_power_sum_reverse`, `rowValue'_split`, `rowValue'_succ_add`, `geom_sum_mul_add_one`, `power_sum_reverse`, `sum_rowValue'_succ_eq`, `rowValue'_sum_index_shift`, `correction_sum_intermediate`.

Not on the F(b) path: `power_sum_closed` (proved but bypassed by Nat-safe approach), `tri_is_triangular` / `tri_tri_is_triangular` (used by Core.lean bridge, not F(b)), concrete evaluations (`tri_two`, `tri_four`, etc.).

**All theorems fully machine-verified** (zero `sorry`).

**Requirements:**
- Lean 4 toolchain (install via `elan`)
- Mathlib (see setup instructions below)
- Run with: `lake build` from the repo root

### FiveTwo.lean
The 5-and-2 pattern — XOR cycle theorem (self-contained, no Mathlib imports).

**Key theorems proven:**
- `xor_cycle_returns` — The G₀ ⊕ G₁ cycle returns to G₀ after 5 states
- `cycle_states` — Proves the cycle visits exactly [G₀, E, G₁, F, G₀]
- `base_ten_factorization` — 10 = 2 × 5

### Primes.lean
Prime list and primesum function.

**Definitions:**
- `firstSevenPrimes` — [2, 3, 5, 7, 11, 13, 17]
- `primesum` — Sum of p^power for each prime in a list

**Key theorems proven:**
- `prime_2` through `prime_17` — Individual primality proofs (via `native_decide`)
- `primesum_7_2` — **primesum([2,3,5,7,11,13,17], 2) = 666**
- `primesum_3_1` — primesum([2,3,5], 1) = 10

### Core.lean
Connecting theorems tying stf to primesum.

**Key theorems proven:**
- `stf_eq_primesum_7_2` — **stf(10) = primesum(7, 2)** (the core identity)
- `stf_ten_is_triangular` — stf(10) is a triangular number
- `chain_tri4_to_tri36` — tri(4) = 10 ∧ stf(10) = 666 ∧ 666 = tri(36)
- `core_pattern` — The full chain: tri(4) = primesum(3,1), stf(tri(4)) = primesum(7,2), and that result is triangular
- `ten_eq_primesum_3_1` — 10 = primesum(3, 1)

### PrimesumMod6.lean
Formal proof that primesum(n, 2) ≡ (n + 5) (mod 6) for all n ≥ 2.

**Key theorems proven:**

*Algebraic core (Part 1):*
- `sq_6k_plus_1_mod6` — (6k+1)² ≡ 1 (mod 6) for all k (ring + omega)
- `sq_6k_plus_5_mod6` — (6k+5)² ≡ 1 (mod 6) for all k (ring + omega)

*Bounded verification (Parts 2–4):*
- `ps_mod6_n3` through `ps_mod6_n7` — Bounded verification for n = 3..7
- `six_divides_666` — 666 % 6 = 0

*General prime square theorem (Part 6):*
- `prime_sq_mod_six` — **∀ p, Prime p → p > 3 → p² % 6 = 1** (primality + interval_cases)

*General primesum induction (Part 7):*
- `nthPrime` — The nth prime via Mathlib's `Nat.nth` (noncomputable)
- `primesumN` — Sum of first n primes raised to a power via `Finset.sum`
- `nthPrime_prime`, `nthPrime_strictMono`, `nthPrime_gt_three` — Helper lemmas
- `primesumN_mod6` — **∀ n ≥ 2, primesumN(n, 2) % 6 = (n + 5) % 6** (induction)

**Corollary:** primesum(n, 2) is divisible by 6 iff n ≡ 1 (mod 6). This provides a necessary condition for stf(b) = primesum(n, 2) — the n value must be congruent to 1 mod 6.

**Mathematical basis:** All primes p > 3 satisfy p = 6k ± 1, therefore p² ≡ 1 (mod 6). The algebraic core (`(6k+1)² % 6 = 1` and `(6k+5)² % 6 = 1`) is fully machine-verified using Mathlib's `ring` tactic + `omega`. The general inductive proof uses Mathlib's `Nat.nth Nat.Prime` for the nth prime definition.

*Dependency chain:*
```
sq_6k_plus_{1,5}_mod6 (algebraic core)
    → prime_sq_mod_six (all primes > 3)
        → primesumN_mod6 (induction using Nat.nth + Finset.sum)
```

### trisum_theorems.md
Documentation of the mathematical theorems, including:
- TriSum definition and closed-form formula
- Recast operation between bases
- The bounded pattern theorem (holds for n=2,3,4, breaks at n=5)
- Open questions about why base-10 appears as a structural boundary

## Lean 4 + Mathlib Setup

The proofs use [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) for tactics like `ring` and access to `Nat.sqrt`.

### Prerequisites

1. **Install elan** (Lean version manager):
   ```bash
   # Windows (PowerShell)
   irm https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex

   # Linux/Mac
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```

2. **Download Mathlib cache** (from the repo root):
   ```bash
   lake exe cache get
   ```
   This downloads ~1.5GB of prebuilt `.olean` files so you don't have to build Mathlib from source (which takes hours).

3. **Build proofs**:
   ```bash
   lake build
   ```

### What gets committed vs installed

| File | Committed? | Purpose |
|------|-----------|---------|
| `lakefile.toml` | Yes | Project config (Mathlib dependency) |
| `lean-toolchain` | Yes | Lean version pinning |
| `lake-manifest.json` | Yes | Dependency lockfile |
| `proofs/**/*.lean` | Yes | Proof source files |
| `.lake/` | **No** (gitignored) | Build artifacts + Mathlib packages |

The `.lake/` directory is restored via `lake exe cache get` — similar to how `node_modules/` is restored via `npm install`.

## Connection to Prime-Square-Sum

The TriSum function `stf(b)` computes the sum of digit-rows in a triangular arrangement:
- `stf(10) = 666` (sum of rows 0123 + 456 + 78 + 9 in base-10)
- This equals the sum of the first 7 squared primes

The proofs here formalize the mathematical foundations that make this relationship possible, particularly the 5/2 structural pattern that appears throughout:
- 5 states from 2 constants in the XOR cycle
- Base-10 = 2 × 5
- The pattern boundary at n=5

## Related Work

These proofs support concepts from:
- [Zero_AG to The Scarcity Framework](https://github.com/Way-of-Scarcity/papers) - Broader mathematical framework
- The 2010 Mathematica notebook in `paper and notes/`
- [docs/rationale.md](../docs/rationale.md) - Why computational exploration discovers these patterns before proofs can formalize them
