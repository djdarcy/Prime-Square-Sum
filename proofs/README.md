# Formal Proofs

This folder contains formal mathematical proofs related to the Prime-Square-Sum conjecture and its connection to triangular number theory.

## Files

### TriSum.lean
Lean 4 formalization of triangular number properties and the XOR cycle theorem.

**Key theorems proven:**
- `tri_one`, `tri_four`, `tri_thirtysix` - Basic triangular number identities
- `xor_cycle_returns` - The G₀ ⊕ G₁ cycle returns to G₀ after 5 states
- `cycle_states` - Proves the cycle visits exactly [G₀, E, G₁, F, G₀]
- Bounded TriSum-Recast theorem verification for n ∈ {2, 3, 4}

**Requirements:**
- Lean 4 toolchain (install via `elan`)
- Run with: `lake env lean TriSum.lean`

### trisum_theorems.md
Documentation of the mathematical theorems, including:
- TriSum definition and closed-form formula
- Recast operation between bases
- The bounded pattern theorem (holds for n=2,3,4, breaks at n=5)
- Open questions about why base-10 appears as a structural boundary

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
