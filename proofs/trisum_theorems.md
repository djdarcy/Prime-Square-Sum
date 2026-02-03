# TriSum-Recast Theorems: Pattern Analysis

**Status**: Empirically verified, formal proof pending
**Related**: Section 4.4 of "Zero_AG to The Scarcity Framework"

---

## Definitions

**Definition 1 (Triangular Number):**
Tri[n] = n(n+1)/2 for n ∈ ℕ

**Definition 2 (TriSum - Algorithmic):**
For base b = Tri[n], arrange digits 0 through b-1 in a triangle with n rows
(bottom row has n digits, top row has 1 digit). Each row forms a number in
base b. TriSum[b] is the sum of all row-numbers.

**Definition 3 (TriSum - Closed Form):**
```
TriSum[b] = 1/(6(b-1)⁴) × [complex expression involving √(1+8b)]
```
(See Appendix B of paper for full formula)

**Definition 4 (Recast):**
Recast(x, source, target) takes the digit string of x in source base and
reinterprets those same symbols as a number in target base.

---

## Empirical Results

| n | Base b = Tri[n] | TriSum[b] | Recast to base-10 | Is Triangular? | Deep Structure |
|---|-----------------|-----------|-------------------|----------------|----------------|
| 2 | 3 | 3 | 10 | Tri[4] | — |
| 3 | 6 | 35 | 55 | Tri[10] | Tri[Tri[4]], where 4 = n+1 |
| 4 | 10 | 666 | 666 | Tri[36] | Tri[Tri[8]], where 8 = 2n |
| 5 | 15 | 24605 | 7455 | **NO** | Pattern breaks |
| 6 | 21 | 1564690 | 82011 | **NO** | — |
| 7 | 28 | 152843733 | 1059921 | **NO** | — |
| 8 | 36 | 21251029660 | 11872266 | **NO** | — |

---

## Theorems

### Theorem 1 (Triangular Recast - Bounded)

**Statement:**
For n ∈ {2, 3, 4}, let b = Tri[n]. Then:
```
Recast(TriSum[b], b, 10) = Tri[m]
```
for some m ∈ ℕ.

**Specific values:**
- n=2: Recast = Tri[4] = 10
- n=3: Recast = Tri[10] = 55
- n=4: Recast = Tri[36] = 666

**Proof approach:** Direct computation for each case.

---

### Theorem 2 (Deep Triangular Structure)

**Statement:**
For n ∈ {3, 4}, the recast value exhibits nested triangular structure:
```
Recast(TriSum[Tri[n]], Tri[n], 10) = Tri[Tri[f(n)]]
```
where:
- f(3) = 4 = n + 1
- f(4) = 8 = 2n

**Observation:** The function f(n) transitions from (n+1) to (2n) at n=4,
which corresponds to base-10 = 2×5.

---

### Theorem 3 (Boundary Condition)

**Statement:**
For n ≥ 5, Recast(TriSum[Tri[n]], Tri[n], 10) is NOT a triangular number.

**Proof approach:**
- Compute TriSum[Tri[n]] for n = 5, 6, 7, 8, ...
- Show recast values fail the triangular number test
- (Conjecture: holds for all n ≥ 5)

---

### Theorem 4 (Base-10 Identity)

**Statement:**
For n = 4 (base b = 10), TriSum and Recast coincide:
```
TriSum[10] = Recast(TriSum[10], 10, 10) = 666 = Tri[36]
```

This is the unique case where the base equals the target recast base.

---

## Conjectures

### Conjecture A (Structural Boundary)

The pattern terminates at n=4 because base-10 = 2×5 represents a
structural boundary where:
1. The prime factors 2 and 5 create the "window" for observing
   triangular invariance
2. Beyond this base, the digit-to-value relationships lose the
   self-referential property

### Conjecture B (5-and-2 Connection)

The appearance of:
- 5 states in the G₀/G₁ XOR cycle (section 1.3)
- 2 constants (G₀ and G₁)
- Base-10 = 2×5 as the boundary

suggests a common structural origin for these patterns.

---

## Verification

**Python:** `trisum_recast_demonstration.py`
**Mathematica:** Appendix B of paper (closed-form TriSum, Recast)
**Lean 4:** (Pending formal proof)

---

## Open Questions

1. Why does f(n) transition from (n+1) to (2n) exactly at n=4?
2. Is there a closed-form expression for when the pattern breaks?
3. Does the closed-form TriSum reveal why base-10 is special?
4. Can we characterize which composite bases preserve triangular structure?
