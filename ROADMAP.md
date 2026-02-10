# Roadmap

## Terminology note

The expression system uses four **directives** (previously called "quantifiers"):

| Directive | Type | Purpose |
|-----------|------|---------|
| `does_exist` | Quantifier (∃) | Find first match satisfying a condition |
| `for_any` | Quantifier (∀-like) | Enumerate all matches / values |
| `verify` | Mode | Evaluate a closed formula — true/false |
| `solve` | Mode | Compute a value or enumerate a sequence |

`does_exist` and `for_any` are true logical quantifiers. `verify` and `solve` are evaluation modes. The term "directive" covers both. As of v0.8.0, `solve` subsumes `verify` (calculator mode with a comparison returns true/false). A future release may deprecate `verify` in favor of `solve`, pending UX evaluation.

---

## Version History

### v0.1.0 (2010)
Original Python 2 implementation. Pickle-based prime storage, basic sieve.

### v0.5.x (Feb 2026)
Python 3 migration, GPU acceleration (CuPy), NumPy prime storage.

- v0.5.0: Python 3 rewrite, primesieve integration, multiprocessing
- v0.5.1: GPU acceleration via CuPy (5x speedup for squared primes)
- v0.5.2: Hybrid GPU/CPU for higher powers

### v0.6.0 (Feb 2026)
Incremental sum caching, digital root utilities. Closed Issues #2, #3, #5, #7, #8.

### v0.7.x — Expression Grammar (Feb 2026)
Major series: built the `--expr` DSL from scratch. Progressed through four phases:

**Phase 1 — Foundation (v0.7.0–v0.7.3)**
- v0.7.0: Triangular functions, FunctionRegistry, sequence generators (#14, #15, #16)
- v0.7.1: Lark LALR parser, AST, `find_matches()` engine (#17)
- v0.7.2: CLI rewrite — `--expr`, `--lhs/--rhs`, decomposed flags (#18)
- v0.7.3: Saved equations (`equations.json`), config system (`config.json`) (#21, #22)

**Phase 2 — Infrastructure (v0.7.4–v0.7.7)**
- v0.7.4: Conda environment, primesieve bindings (#28)
- v0.7.5: Multi-algorithm sieve system — basic/segmented/individual (#29)
- v0.7.6: `verify` directive/quantifier, VSCode debug config (#34, #32)
- v0.7.7: Iterator protocol — int/float, dtype validation, linspace (#37, #20)

**Phase 3 — Operators & Functions (v0.7.8–v0.7.10)**
- v0.7.8: Math builtins — pow, abs, mod, sqrt, floor, ceil (#44 Phase 1)
- v0.7.9: Function namespaces — math.*, pss.*, user.* (#46)
- v0.7.10: Unified `--list CATEGORY` command (#47–#50)

**Phase 4 — Advanced Operators (v0.7.12–v0.7.19)**
- v0.7.12: Arithmetic operators, expression validation (#44 Phase 2)
- v0.7.14: Boolean/bitwise operators, chained comparisons, context blocks (#44 Phase 3a)
- v0.7.17: `^` precedence fix via contextual lexing (#52)
- v0.7.18: Complex number functions — complex(), real(), imag(), conj() (#54 Phase 1)
- v0.7.19: Imaginary literal syntax, opt-in via config (#54 Phase 2)

**Lean 4 Proofs (v0.7.11–v0.7.21, interleaved)**
- v0.7.11: Lean 4 + Mathlib setup, `tri_is_triangular` proved
- v0.7.13: Core identity `stf(10) = primesum(7,2) = 666`, stf merged into proofs
- v0.7.15: Digits.lean — recast, digitalRoot, casting-out theorem
- v0.7.16: Bridge lemma — algorithmic ↔ algebraic rowValue equivalence
- v0.7.20: Algebraic decomposition, telescoping stf, recursive relation
- v0.7.21: Boundary sum closed form

---

## v0.8.x — Enumeration & Solving (current)

The 0.8.x series focuses on making the expression system a general-purpose mathematical exploration tool, moving beyond search-and-match into computation, enumeration, and eventually algebraic solving.

### v0.8.0 (done)
- `solve` directive — calculator mode, value enumeration, implicit detection
- Bare-term expressions — `for_any tri(n)` enumerates without needing a comparison
- Graceful CTRL+C for long enumerations
- 812 tests

### v0.8.1 (done)
- Multi-level verbosity (`-v`/`-vv`/`-vvv`), `--quiet`/`-Q`, `--limit N` (#31, #53)
- Output library (`utils/output.py`) and domain hints (`utils/hints.py`) (#57)
- All verbose output to stderr (clean stdout for data)
- 846 tests

### v0.8.x goals (remaining)

**Directive cleanup**
- Evaluate `verify` deprecation — `solve expr == value` already returns true/false (#45)
- Rename "quantifier" to "directive" in code, docs, and CLI help (#45)
- Reduce overlap between `solve` and `for_any` for bare-term expressions

**Iterator improvements**
- Multi-variable strategies: product, parallel, zip, adaptive (#42)
- Stateful iterators: Fibonacci-indexed, prime-indexed (#39)
- Custom step functions (#38)
- Resume/continue support (`--start-n`) (#26)
- Indefinite / unbounded iteration (#25)

**Smart termination**
- Monotonicity-aware auto-termination (#41)
- Value-based bounds (`--max-lhs-value`) (#40)
- Early termination for monotonic sequences (#23)

**Output and UX**
- Channel filtering (`--channels progress,timing`) — Phase 2 of output library
- Runtime verbosity toggle (signal-based mid-stream control) — Phase 2
- Configurable output formatting (#55)
- Enhanced JSON with expression context (#35)

---

## v0.9.x — Caching & Performance (planned)

- Multi-sequence cache architecture (#19)
- Cache inspection and export tools (#10)
- Prime source integration and import/export (#9)
- OEIS-style sequence storage (#6)
- Algorithm variant system for FunctionRegistry (#30)
- Bit-packed sieve for memory efficiency (#33)
- GPU acceleration for user functions (#27)

## v1.0 — Maturity (planned)

- Stable CLI interface
- Output destination routing — `--output file/clip/stdout/all` (#59)
- Algebraic solving via `solve` (Newton's method, bisection, inverse lookup)
- Expression language documentation finalized
- Lean proofs for core identities complete (#56)
- Performance benchmarks published (#11, #12)
- Distributed computing (#1)

---

## Research tracks (ongoing)

These are not version-gated — they progress as insights emerge:

- Triangular depth conjectures and stf(666) (#43)
- Formal proof: closed-form stf(b) (#56)
- Pascal-weighted number system analysis
- 5-and-2 XOR cycle patterns
