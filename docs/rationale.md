# Why This Tool Exists: Computational Irreducibility

Prime-Square-Sum isn't just a brute-force iterator. It exists because certain mathematical relationships **cannot be solved analytically** - they can only be discovered through computation.

## The Core Question

This project investigates whether `stf(666)` - a 98-digit number derived from triangular row sums - equals a sum of primes raised to some power:

```
stf(666) = 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290

Does there exist n and p such that: primesum(n, p) = stf(666)?
```

The only way to find out is to **compute and check**.

## Closed-Form vs Irreducible Functions

Not all mathematical functions are created equal:

### Functions with Closed-Form Inverses

Some functions can be inverted algebraically:

| Function | Forward | Inverse |
|----------|---------|---------|
| `tri(n) = (n² + n) / 2` | `tri(36) = 666` | `qtri(666) = (-1 + √5329) / 2 = 36` |
| `pow(n, 2) = n²` | `pow(5, 2) = 25` | `√25 = 5` |
| Polynomial roots | `(n+3)² = 49` | Quadratic formula: `n = 4` |

For these, the expression system is **convenient** but not **necessary** - you could solve them on paper.

### Computationally Irreducible Functions

Prime-based functions have no closed-form inverse:

```
primesum(n, 2) = p₁² + p₂² + p₃² + ... + pₙ²
primesum(7, 2) = 4 + 9 + 25 + 49 + 121 + 169 + 289 = 666
```

**Why is this irreducible?**

1. **No formula for the nth prime**: There's no closed-form expression `p(n)` that directly computes the nth prime
2. **No inverse for prime sums**: Given a target like 666, you can't algebraically solve for n
3. **Enumeration is required**: The only way to find `primesum⁻¹(666, 2) = 7` is to compute forward

This is the mathematical concept of [computational irreducibility](https://en.wikipedia.org/wiki/Computational_irreducibility) - no shortcut exists; you must run the computation.

## What This Tool Provides

Prime-Square-Sum makes exploring irreducible relationships practical:

1. **Efficient enumeration**: Optimized sieving (primesieve) generates primes at ~125M/sec
2. **Incremental caching**: Track cumulative sums without recomputing from scratch
3. **Expression grammar**: Query arbitrary relationships: `primesum(n,2) == tri(m)`
4. **Pattern discovery**: Find relationships that can't be derived analytically

### Example: The Original Discovery

The relationship `stf(10) = 666 = primesum(7, 2)` wasn't solved algebraically - it was discovered by computation, then verified symbolically.

## What Patterns CAN Help (But Don't Fully Solve It)

### Prime Distribution Patterns

Primes > 3 are of the form `6k ± 1`. This helps **sieving** (skip 66% of candidates) but doesn't provide the nth prime directly.

### Pascal's Triangle Connection

Powers of 11 embed Pascal coefficients:
```
11¹ = 11      → {1, 1}
11² = 121     → {1, 2, 1}
11³ = 1331    → {1, 3, 3, 1}
11⁴ = 14641   → {1, 4, 6, 4, 1}
```

This generalizes across number bases (the Mathematica `PascalRow` function in the original notebook demonstrates this empirically). The same {1, 4, 6, 4, 1} coefficients from Pascal Row 4 define a weighted number system in which stf(b) values can be represented. When stf(b) is divisible by 6, the representation collapses to a "pure center" pattern: **{0, 0, X, 0, 0}** — meaning the value is carried entirely by the central weight (6).

This connects directly to our proof work: we've formally proven that `primesum(n, 2) % 6 = (n + 5) % 6`, meaning primesum is divisible by 6 only when n ≡ 1 (mod 6). Conjecture 5 observes that stf(tri(k²)) is divisible by 6 precisely when r is a perfect square — the two mod 6 conditions constrain the search from both sides. See [conjectures.md](../paper%20and%20notes/conjectures.md#conjecture-5-the-stf-k²-divisibility-conjecture) for details.

### Composite Base Sieving

Techniques like examining digit patterns in composite bases can help identify composites, but don't provide prime formulas.

## The Value of Exploration

This tool enables **empirical mathematics**:

- Test conjectures computationally before attempting proofs
- Discover unexpected relationships (like stf(10) = 666 = tri(36))
- Explore chains of triangular numbers and prime sums
- Verify patterns across massive search spaces

The goal isn't just to find answers - it's to find **patterns worth proving**.

The mod 6 pattern is a concrete example: bounded computation discovered that primesum(n, 2) follows a cyclic pattern mod 6, which was then formally proven by induction in Lean 4 (see [proofs/](../proofs/)). Similarly, the Pascal Row 4 "pure center" pattern was discovered computationally and connects to an open conjecture about perfect-square triangular bases.

## Verification

Run the verification script to confirm the core relationships:

```bash
python verification/verify_stf666.py
```

This verifies that `stf(666)` equals the 98-digit target value that the project investigates.

## See Also

- [README.md](../README.md) - Project overview and the stf(10) = 666 discovery
- [expressions.md](expressions.md) - Expression syntax for querying relationships
- [paper and notes/](../paper%20and%20notes/) - Original Mathematica notebook with theoretical background
- [conjectures.md](../paper%20and%20notes/conjectures.md) - Open conjectures including the stf-k² divisibility pattern
- [proofs/](../proofs/) - Formal Lean 4 proofs (prime_sq_mod_six, primesumN_mod6, stf = primesum chain)
