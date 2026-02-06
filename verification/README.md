# Verification Scripts

Computational verification of the TriSum/Recast mathematical patterns.

## Files

### verify_stf666.py
Verifies that `stf(666)` equals the 98-digit target value from the README.

**What it tests:**
- Confirms 666 is triangular: `tri(36) = 666`
- Computes `stf(666) = trisum(666, 36)` (36 rows in base-666)
- Verifies result matches: `37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290`

**Why this matters:**
This 98-digit number is the target that Prime-Square-Sum investigates. The question: does there exist `n` and `p` such that `primesum(n, p) = stf(666)`? Since `primesum()` is computationally irreducible (no closed-form inverse), we must enumerate and check.

**Usage:**
```bash
python verify_stf666.py
```

---

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
- `stf(666)` produces the 98-digit target that the project investigates
- The pattern breaking at n=5 suggests base-10 (= 2×5) is a structural boundary
- This connects to the 5/2 pattern observed throughout the mathematical framework

See [docs/rationale.md](../docs/rationale.md) for why these relationships require computational exploration rather than analytical solution.

## Related Work

- `proofs/TriSum.lean` - Formal Lean 4 proofs of these properties
- [Zero_AG to The Scarcity Framework](https://github.com/Way-of-Scarcity/papers) - Theoretical foundation
