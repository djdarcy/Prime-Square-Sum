# Verification Scripts

Computational verification of the TriSum/Recast mathematical patterns.

## Files

### trisum_recast_demonstration.py
Python script that empirically verifies the TriSum-Recast triangular pattern.

**What it tests:**
```
For n in {2, 3, 4, 5, 6, 7, 8}:
  1. Compute base = Tri[n]
  2. Compute TriSum[base] using closed-form formula
  3. Recast the result to base-10
  4. Check if the recast value is triangular
```

**Key findings:**
| n | Base | TriSum | Recast to Base-10 | Triangular? |
|---|------|--------|-------------------|-------------|
| 2 | 3    | 3      | 10                | Yes (Tri[4]) |
| 3 | 6    | 35     | 55                | Yes (Tri[10]) |
| 4 | 10   | 666    | 666               | Yes (Tri[36]) |
| 5 | 15   | 24605  | 7455              | **No** |

The pattern holds for n ∈ {2, 3, 4} and breaks at n = 5.

**Usage:**
```bash
python trisum_recast_demonstration.py
```

**Requirements:**
- Python 3.8+
- No external dependencies (uses only stdlib)

## Connection to Prime-Square-Sum

This verification supports the core conjecture:
- `stf(10) = 666` is both triangular AND equals the sum of first 7 squared primes
- The pattern breaking at n=5 suggests base-10 (= 2×5) is a structural boundary
- This connects to the 5/2 pattern observed throughout the mathematical framework

## Related Work

- `proofs/TriSum.lean` - Formal Lean 4 proofs of these properties
- [Zero_AG to The Scarcity Framework](https://github.com/Way-of-Scarcity/papers) - Theoretical foundation
