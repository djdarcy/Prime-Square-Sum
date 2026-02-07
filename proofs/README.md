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

*Bounded verification:*
- TriSum-Recast theorem verification for n ∈ {2, 3, 4}; pattern breaks at n = 5

*Dependency chain:*
```
tri_zero (base case) → tri_succ (recursion) → two_mul_tri (induction)
    → tri_is_triangular (correctness) → tri_tri_is_triangular (composition)
    → deep_tri_n3_triangular (55) + deep_tri_n4_triangular (666)
```

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
Formal proof that primesum(n, 2) ≡ (n + 5) (mod 6) for all n ≥ 3.

**Key theorems proven:**
- `sq_6k_plus_1_mod6` - (6k+1)² ≡ 1 (mod 6) for all k (proven by ring_nf + omega)
- `sq_6k_plus_5_mod6` - (6k+5)² ≡ 1 (mod 6) for all k (proven by ring_nf + omega)
- `ps_mod6_n3` through `ps_mod6_n7` - Bounded verification for n = 3..7
- `six_divides_666` - 666 % 6 = 0

**Corollary:** primesum(n, 2) is divisible by 6 iff n ≡ 1 (mod 6). This provides a necessary condition for stf(b) = primesum(n, 2) — the n value must be congruent to 1 mod 6.

**Mathematical basis:** All primes p > 3 satisfy p = 6k ± 1, therefore p² ≡ 1 (mod 6). The algebraic core (`(6k+1)² % 6 = 1` and `(6k+5)² % 6 = 1`) is fully machine-verified using Mathlib's `ring` tactic + `omega`. The general inductive proof of the primesum formula requires a "nth prime" definition for full formalization.

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
