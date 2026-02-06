# Conjectures and Observations

Speculative patterns observed during investigation of the stf(b) and primesum relationships. These are documented for further investigation - some may be numerical coincidences, others may reveal deeper structure.

---

## The Core Pattern (Established)

The known chain of relationships:

| Step | Relationship | Note |
|------|--------------|------|
| 1 | tri(4) = 10 | 4th triangular number |
| 2 | 10 = primesum(3, 1) | Sum of first 3 consecutive primes, power 1 |
| 3 | stf(10) = 666 | Triangular row sum in base 10 |
| 4 | 666 = primesum(7, 2) | Sum of first 7 consecutive squared primes |
| 5 | 666 = tri(36) | 666 is also triangular |

**Open question**: Does stf(666) = primesum(n, p) for some n, p?

---

## Conjecture 1: Triangular Depth Correlation

### Observation

Define **triangular depth** as the number of times qtri() can be applied before reaching a non-triangular number:

```
depth(666) = 2:  666 → qtri → 36 → qtri → 8 → STOP (8 not triangular)
depth(10)  = 1:  10  → qtri → 4  → STOP (4 not triangular)
```

### Conjecture

The power p in primesum(n, p) correlates with the triangular depth of the result:

| Expression | Result | Triangular Depth | Power |
|------------|--------|------------------|-------|
| primesum(3, 1) | 10 | 1 | 1 |
| primesum(7, 2) | 666 | 2 | 2 |
| primesum(?, 3) | ? | 3? | 3 |

**Prediction**: If stf(666) = primesum(n, 3), then stf(666) should have triangular depth 3.

### Status

- [ ] Verify stf(666) is NOT triangular (known, but verify depth = 0)
- [ ] Search for primesum(n, 3) values with depth 3
- [ ] Check if any triangular numbers with depth ≥ 3 appear in prime power sums

---

## Conjecture 2: Powers of 2 in Triangular Inverses

### Observation

The qtri() values in the depth chains are powers of 2:

```
qtri(10)  = 4 = 2²
qtri(666) = 36, and qtri(36) = 8 = 2³
```

The exponents (2, 3) are the first two primes.

### Conjecture

If the pattern continues:
- Depth-3 triangular: qtri chain reaches 2⁵ = 32 (next prime exponent is 5)
- tri(32) = 528

**Question**: Does 528 appear anywhere in the primesum/stf relationships?

### Status

- [ ] Check if 528 is a primesum value
- [ ] Check if stf(528) has interesting properties
- [ ] Investigate whether 2^p (p prime) appears systematically

---

## Conjecture 3: Mersenne-Adjacent Prime Indices

### Observation

The n values in primesum(n, p) that produce triangular results:

| n | Power | Result | n relation to 2^k |
|---|-------|--------|-------------------|
| 3 | 1 | 10 | 3 = 2² - 1 (Mersenne) |
| 7 | 2 | 666 | 7 = 2³ - 1 (Mersenne prime) |

Both 3 and 7 are Mersenne numbers (2^k - 1) and both happen to be prime.

### Conjecture (Weak)

The pattern might involve Mersenne numbers: n = 2^(p+1) - 1

| Power p | Predicted n | Is n prime? | primesum(n, p) |
|---------|-------------|-------------|----------------|
| 1 | 2² - 1 = 3 | Yes | 10 ✓ |
| 2 | 2³ - 1 = 7 | Yes | 666 ✓ |
| 3 | 2⁴ - 1 = 15 | No (3×5) | ? |

**Problem**: 15 is not prime, so the "Mersenne prime" aspect breaks. However, the Mersenne number pattern (2^k - 1) might still hold.

### Status

- [ ] Compute primesum(15, 3)
- [ ] Check if result is triangular or relates to stf(666)
- [ ] Look for alternative patterns in the (n, p) pairs

---

## Conjecture 4: Maximally Nested Triangulars

### Observation

Starting from 2 (the first prime), repeatedly applying tri():

```
a(0) = 2
a(1) = tri(2) = 3
a(2) = tri(3) = 6
a(3) = tri(6) = 21
a(4) = tri(21) = 231
a(5) = tri(231) = 26796
...
```

This sequence: 2, 3, 6, 21, 231, 26796, ...

### Conjecture

Numbers in this sequence may have special properties related to prime sums:
- 3 = primesum(2, 1) = 2 + 3 - 2 ... hmm, not quite
- 6 = primesum(3, 1) - 4 = 10 - 4 ... also not clean
- 21 = ?

**Alternative**: The sequence represents "triangular depth towers" - numbers with maximal nesting depth for their magnitude.

### Status

- [ ] Check OEIS for this sequence
- [ ] Investigate if any terms relate to primesum values
- [ ] Explore relationship to iterated function theory

---

## Observation: The 5/2 Boundary

### Context

From `trisum_recast_demonstration.py`, the triangular recast pattern holds for n ∈ {2, 3, 4} and breaks at n = 5.

Base 10 = 2 × 5, suggesting the 5/2 factorization may be a structural boundary.

### Connection

This may relate to why stf(10) produces such clean results (666 = triangular = prime sum), while larger triangular bases don't.

### Status

- [ ] Investigate other bases of form 2p (where p is prime)
- [ ] Check stf() for bases 6, 10, 14, 22, 26, ...

---

## Notation Reference

| Symbol | Meaning |
|--------|---------|
| tri(n) | nth triangular number: n(n+1)/2 |
| qtri(x) | Inverse triangular: n such that tri(n) = x, or undefined |
| stf(b) | Triangular row sum function for base b |
| primesum(n, p) | Sum of first n primes raised to power p |
| depth(x) | Triangular depth: iterations of qtri() before non-triangular |

---

## See Also

- [2010 Mathematica Notebook](./2010%20-%20Recurrence%20relation%20between%20triangular%20numbers%20and%20squared%20primes%20-%20D.%20Darcy.nb) - Original investigation
- [docs/rationale.md](../docs/rationale.md) - Why computational exploration is necessary
- [verification/](../verification/) - Computational verification scripts
