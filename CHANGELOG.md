# Changelog

All notable changes to this project will be documented in this file.

## [0.7.20] - 2026-02-08

### Added
- **Phase 3C: Algebraic decomposition and recursive relation** in TriSum.lean
  - `rowValue'_split` — decompose rowValue' into constant-coefficient geometric sum plus linearly-weighted power sum
  - `stf'` definition — algebraic Finset.sum form of stf using rowValue'
  - `stf_eq_stf'` — bridge algorithmic stf (List.foldl) to algebraic stf' (Finset.sum), via `list_foldl_add_eq_finset_sum` helper
  - `rowValue'_succ_add` — recursive relation: rowValue'(b, z+1) in terms of b * rowValue'(b, z) with geometric sum correction, additive form avoids Nat subtraction underflow
  - `geom_sum_mul_add` — division-free geometric series recursion: b * Σ b^i + 1 = Σ b^i over extended range
  - `power_sum_reverse` — descending powers equal ascending via sum_flip
  - Bounded `native_decide` verifications for all new theorems
- Updated `proofs/README.md` with Phase 3B and 3C theorem documentation

### Design Documents
- `2026-02-08__06-49-01__DISCUSS_Rnd3_FINAL_ASSESSMENT_rowValue-recursive-relation.md` — collaborate2 final assessment for recursive relation strategy
- `2026-02-08__07-31-00__full-postmortem_phase-3c-algebraic-decomposition-recursive-relation.md` — Phase 3C postmortem

## [0.7.16] - 2026-02-07

### Added
- **Phase 3B: Bridge lemma and algebraic rowValue** in TriSum.lean (Part 4b)
  - `rowValue'` — algebraic Finset.sum definition with positional powers
  - `digitsToNat_eq_ofDigits_reverse` — connects big-endian foldl to Mathlib's little-endian `ofDigits` via `List.reverse`
  - `digitsToNat_arith_seq` — core bridge lemma: foldl over arithmetic sequence [c, c+1, ..., c+z-1] equals Finset.sum with positional weights, proved by induction on z
  - `rowValue_eq_rowValue'` — general equivalence between algorithmic and algebraic rowValue (no sorry)
  - Bounded verification via `native_decide` for bases 6, 10, 15
  - Helper lemmas: `digitsToNat_append_single`, `range_map_succ`
- Bridge lemma Python verification script (`tests/one-offs/thinking/2026-02-07__bridge-lemma-verification.py`)
- **Approach B wired as primary proof** of `digitsToNat_arith_seq` in TriSum.lean
  - `reverse_arith_seq_succ` — reversed arithmetic sequence decomposes as cons
  - `ofDigits_reversed_arith_seq` — little-endian form: `ofDigits b (reversed seq) = Σ (c+z-1-i)*b^i`, proved by induction using `ofDigits_cons` + `sum_range_succ'`
  - `digitsToNat_arith_seq` now uses compositional three-step chain: `digitsToNat_eq_ofDigits_reverse` → `ofDigits_reversed_arith_seq` → `Finset.sum_flip` re-indexing
  - Approach A helpers (`digitsToNat_append_single`, `range_map_succ`) kept for reference
  - BridgeB.lean retired to `private/baks/` (theorems consolidated into TriSum.lean)

### Design Documents
- `2026-02-07__17-11-30__dev-workflow_phase3b-bridge-lemma-rowvalue-algebraic.md` — analysis for Phase 3B approach
- `2026-02-08__00-44-29__dev-workflow_approach-b-primary-sum-flip-reindexing.md` — analysis for wiring Approach B as primary

## [0.7.15] - 2026-02-07

### Added
- **New proof file: `Digits.lean`** — general digit operations module
  - `recast(source_base, target_base, x)` using Mathlib's `Nat.digits` + `Nat.ofDigits`
  - Both are little-endian, so the composition is direct with no list reversal
  - Fully encapsulates the Mathematica `Recast` function — the Mathematica version
    routes through string representation (`CustomIntegerString`, `CustomFromDigits`,
    `digitList`) to support display of arbitrary bases including a 666-symbol alphabet
    (digits, Latin, Greek, Hebrew, Cyrillic, Hiragana, Katakana, CJK). Our Lean
    definition works on numeric digit values directly, so the character-mapping
    layer is unnecessary. Full Mathematica source documented in Digits.lean.
  - `recast_self` — round-trip identity: `recast b b x = x`
  - `digitSum` — sum of digits in base b (wraps `Nat.digits`)
  - `digitCount` — number of digits in base b
  - `digitalRoot` — O(1) formula `1 + ((n-1) % (b-1))` for arbitrary bases
  - `digitSum_mod` — general casting-out theorem: `n ≡ digitSum b n [MOD (b-1)]`
  - Concrete verifications: `digitSum 10 666 = 18`, `digitCount 10 666 = 3`,
    `digitalRoot 10 666 = 9`, `digitCount 666 665 = 1` (compression point)
- **TriSum.lean refactored** — digit operations moved to Digits.lean
  - Bounded recast theorems (`recast_stf_n{2,3,4,5}`) remain in TriSum.lean
    since they combine recast with stf/tri
  - Upgraded triangularity theorems now use `recast` expressions instead of
    hardcoded values (10, 55, 666, 7455)
- 3 thinking scripts documenting sympy analysis of tf numerator factoring:
  - tf(b,z) numerator factors as `2*(b-1)^2 * Q(b,z)` where Q is a pure polynomial
  - Q(b,z) coefficient patterns and recursive relations identified
  - Verified Q = rowValue across bases {3, 6, 10, 15, 45}

### Design Documents
- `2026-02-07__13-23-27__DISCUSS_Rnd{1-4}_*_phase3-lean-tf-recast-strategy.md` — 3-round Gem discuss + independent assessment
- `2026-02-07__15-27-09__dev-workflow_lean-digit-meta-formalizations.md` — analysis for digit meta additions

## [0.7.13] - 2026-02-07

### Added
- **Lean 4 + Mathlib v4.27.0 infrastructure**
  - `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` at repo root
  - Unified library (`PrimeSquareSum`) with 5 proof modules
  - `.gitignore` updated for `.lake/` build artifacts
- **Core identity proved: stf(10) = primesum(7, 2) = 666**
  - `stf_eq_primesum_7_2` — machine-verified identity linking triangular digit sums to squared primes
  - `core_pattern` — the full chain: tri(4) = primesum(3,1), stf(tri(4)) = primesum(7,2), result is triangular
- **`tri_is_triangular` proved** — last `sorry` eliminated, all proofs fully machine-verified
  - Uses `Nat.sqrt`, `Nat.even_mul_succ_self`, `ring` to show `isTriangular(tri(n)) = true` for all n
  - Proves the discriminant `1 + 8·tri(n) = (2n+1)²` is always a perfect square
- **New theorems in TriSum.lean** (Part 7 synthesis section)
  - `tri_zero` — base case: tri(0) = 0
  - `two_mul_tri` — division-free formula: 2·tri(n) = n·(n+1), proved by induction
  - `tri_tri_is_triangular` — composition: tri(tri(n)) is always triangular
  - `tri_plus_succ_is_triangular` — chaining: tri(n)+(n+1) is triangular
  - `deep_tri_n3_triangular` — 55 is triangular via tri(tri(4)), not computation
  - `deep_tri_n4_triangular` — 666 is triangular via tri(tri(8)), not computation
- **stf function merged into TriSum.lean** — algorithmic definitions for the digit-row sum
  - `digitsToNat`, `qg`, `rowValue`, `stf` definitions
  - `stf_ten` — stf(10) = 666 (via `native_decide`)
  - Bounded recast pattern verification for n ∈ {2, 3, 4}; breaks at n = 5
- **New proof file: `FiveTwo.lean`** — XOR cycle / 5-and-2 pattern
  - Self-contained (no Mathlib imports, pure Boolean logic)
  - `xor_cycle_returns`, `cycle_states`, `base_ten_factorization`
- **New proof file: `Primes.lean`** — prime list and primesum
  - `firstSevenPrimes`, `primesum` definitions
  - Individual primality proofs (`prime_2` through `prime_17`)
  - `primesum_7_2` = 666, `primesum_3_1` = 10
- **New proof file: `Core.lean`** — connecting theorems
  - `stf_eq_primesum_7_2`, `stf_ten_is_triangular`, `chain_tri4_to_tri36`, `core_pattern`
- **New proof file: `PrimesumMod6.lean`**
  - primesum(n,2) ≡ (n+5) mod 6 for all n ≥ 2
  - Algebraic core: (6k+1)² % 6 = 1 and (6k+5)² % 6 = 1 (ring + omega)
  - Bounded verification for n = 3..7
  - `prime_sq_mod_six` — ∀ p, Prime p → p > 3 → p² % 6 = 1 (primality + interval_cases)
  - `primesumN_mod6` — ∀ n ≥ 2, primesumN(n,2) ≡ (n+5) mod 6 (induction via Nat.nth + Finset.sum)
  - Uses Mathlib's `Nat.nth Nat.Prime` for nth prime, `Finset.sum` for summation
- **Conjecture 5** (stf-k² pattern) added to `paper and notes/conjectures.md`
- **`utils/pascal_systems.py`** — Pascal-weighted number system analytical tools
- 12 verification/thinking scripts in `tests/one-offs/thinking/`
- **Updated `docs/rationale.md`** — Pascal's Triangle connection now links to the Pascal-weighted number system, the "{0, 0, X, 0, 0}" pure center pattern, proven primesum mod 6 theorem, and Conjecture 5

### Technical Notes
- Unified library structure: single `[[lean_lib]]` with `roots` array enables cross-module imports
- Proof dependency chain: tri_zero → tri_succ → two_mul_tri → tri_is_triangular → tri_tri_is_triangular
- Core.lean imports TriSum + Primes + PrimesumMod6 to prove the connecting identity
- Structural proofs for 55 and 666 avoid `native_decide` by composing general theorems
- PrimesumMod6 proof chain: sq_6k_plus_{1,5}_mod6 → prime_sq_mod_six → primesumN_mod6
- Gem consulted for proof strategy and project organization; API names verified against Mathlib source

### Design Documents
- `2026-02-06__16-16-09__full-postmortem_tri-is-triangular-proof-and-synthesis.md`
- `2026-02-06__15-27-22__full-postmortem_pascal-exploration-lean-mathlib-setup.md`

## [0.7.10] - 2026-02-06

### Added
- **Unified `--list CATEGORY` command** (Issue #47)
  - Consolidates `--list-functions`, `--list-equations`, `--list-algorithms`, `--show-config`
  - `--list` bare shows available categories with counts
  - `--list all` shows all categories (equations > functions > algorithms > config)
  - Categories: `functions`, `equations`, `algorithms`, `config`, `all`
- **`utils/list_commands.py`** — Extracted list handlers from prime-square-sum.py
- **`scripts/gh_sub_issues.py`** — Tool for managing GitHub sub-issue relationships
- 10 new CLI integration tests (571 total)

### Changed
- Removed `--list-functions`, `--list-equations`, `--list-algorithms`, `--show-config` flags
- Cleaned up prime-square-sum.py imports (list/display logic moved to utils/list_commands.py)

### Related Issues
- Issue #47: Consolidate --list-* flags (parent)
- Issue #48: Add --list CATEGORY unified flag
- Issue #49: Deprecate old flags (removed instead — personal tool)
- Issue #50: Update docs for --list syntax

## [0.7.9] - 2026-02-06

### Added
- **Function namespace system** (Issue #46)
  - Three namespaces: `math.*`, `pss.*`, `user.*`
  - Qualified names always resolve: `math.pow(2, 10)`, `pss.tri(36)`
  - Unqualified names resolve by priority: user > pss > math
  - Dotted name support in Lark grammar
  - `--list-functions` output grouped by namespace
  - `--list-equations` now shows compact function summary at bottom
- **Auto-registered Python math module** under `math.*` namespace
  - All 53 callable functions from Python's `math` module
  - Includes: sin, cos, tan, log, exp, gcd, lcm, gamma, erf, and more
  - Custom wrappers for pow (int-preserving), sqrt (perfect-square detection),
    floor, ceil, abs, mod
- **User function namespacing** via `--functions`
  - User functions registered under `user.*` namespace
  - Collisions handled via priority (user wins unqualified, builtins preserved qualified)
  - No warnings for expected namespace collisions
- 32 new tests (namespace resolution, dotted name parsing, integration) - 561 total

### Changed
- `FunctionSignature` now includes `namespace` field
- `FunctionRegistry` uses dual registration (qualified + unqualified)
- `--list-functions` displays grouped by namespace with priority note

### Related Issues
- Issue #46: Function namespace and collision prevention
- Issue #44: Grammar arithmetic operators (sub-issue parent)

### Design Documents
- `2026-02-06__09-16-47__function-namespace-collision-prevention.md`

## [0.7.8] - 2026-02-06

### Added
- **Math function builtins** (Issue #44 Phase 1)
  - `pow(base, exp)` - exponentiation, replaces `square()`
  - `abs(x)` - absolute value
  - `mod(a, b)` - modulo with division-by-zero validation
  - `sqrt(x)` - square root, returns int for perfect squares
  - `floor(x)` - round down to nearest integer
  - `ceil(x)` - round up to nearest integer
  - Wrappers provide proper `inspect.signature()` support
- 20 new math function tests - 529 total tests passing

### Removed
- **`square()` function** removed from `utils/sequences.py` and FunctionRegistry
  - Use `pow(x, 2)` instead
  - Eliminates collision risk with user-defined `square()` via `--functions`

### Related Issues
- Issue #44: Extend expression grammar with math functions (Phase 1 complete)
- Issue #46: Function namespace and collision prevention (motivated by growing builtin count)

### Design Documents
- `2026-02-05__21-59-32__grammar-arithmetic-operators-analysis.md`
- `2026-02-06__09-16-47__function-namespace-collision-prevention.md`

## [0.7.7] - 2026-02-05

### Added
- **Iterator system with type coercion foundation** (Issues #37, #20)
  - `utils/types.py` - Centralized type validation utilities
    - `_ensure_int()` - Accept integral floats (7.0), reject non-integral (7.5)
    - `_ensure_int32/64()`, `_ensure_uint64()` - Bounded integer validation
    - `_ensure_float32/64()` - Float bounds validation for GPU compatibility
  - `utils/iterators.py` - Iterator protocol for sequence enumeration
    - `SequenceIterator` ABC with `__iter__`, `__next__`, `current`, `exhausted`
    - `IntIterator` - Integer iteration with dtype bounds validation
    - `FloatIterator` - Float iteration using Decimal for precision
    - `num_steps` linspace-style mode for FloatIterator
- **CLI iterator flags**
  - `--iter-var VAR:START:STOP[:STEP][:DTYPE]` - Compact iterator syntax
  - `--iter-type`, `--iter-start`, `--iter-stop`, `--iter-step` - Individual flags
  - `--iter-num-steps` - Linspace mode (compute step from count)
  - `--iter-dtype` - Type constraint (int32, int64, uint64, float32, float64)
- **Documentation**
  - `docs/rationale.md` - Why this tool exists (computational irreducibility)
  - `paper and notes/conjectures.md` - Triangular depth observations
  - `verification/verify_stf666.py` - Verifies stf(666) = 98-digit number
- 103 new tests (75 iterator + 28 type coercion) - 515 total tests passing

### Changed
- `find_matches()` now accepts `iterator_factories` parameter (backwards compatible)
- Type validation applied consistently to: `tri()`, `qtri()`, `trisum()`, `primesum()`, `fibonacci()`, `factorial()`, `catalan()`
- README.md updated with rationale link and improved clarity

### Technical Notes
- FloatIterator uses `decimal.Decimal` internally to avoid floating-point precision issues
- dtype validation ensures compatibility with primesieve (uint64) and cupy (int32/int64)
- Iterator factories allow lazy construction for memory efficiency

### Related Issues
- Issue #37: Basic iterator protocol (closes)
- Issue #20: Handle numeric type coercion (closes)
- Issue #24: Custom Iterator Functions epic (partial - #37 complete)
- Issue #43: Triangular depth conjectures (documentation added)

### Design Documents
- `2026-02-05__15-11-13__v077-implementation-plan.md`
- `2026-02-05__17-34-25__v077-v08x-implementation-roadmap.md`

## [0.7.6] - 2026-02-05

### Added
- **`verify` quantifier for closed formulas** (Issue #34)
  - Explicit: `--expr "verify primesum(7,2) == 666"` returns `true`/`false`
  - Implicit: `--expr "primesum(7,2) == 666"` auto-detects verify mode (no free variables)
  - JSON output: `{"verified": true}` or `{"verified": false}`
  - `verify_expression()` convenience function in grammar module
- **VSCode debug configuration** (Issue #32)
  - `.vscode/launch.json` with 7 configurations:
    - "Verify Expression" - test verify quantifier
    - "Target 666" - standard target search
    - "Target with Algorithm" - test sieve algorithms
    - "Expression Query" - test does_exist quantifier
    - "Run All Tests" - pytest integration
    - "Debug Current File" - generic debugging
    - "Custom Command" - user input prompt for any arguments
  - `.vscode/settings.json` with Python testing config
  - `.vscode/` removed from `.gitignore` for shared configs
- `verify-stf10` equation added to `equations.json` - verifies stf(10) = 666
- **Documentation** for expression system
  - `docs/expressions.md` - Expression syntax, quantifiers, operators
  - `docs/equations.md` - Saved equations and `equations.json` format
  - `docs/functions.md` - Function reference and custom functions
- 17 new tests for verify quantifier

### Removed
- **`--verify` flag deprecated and removed**
  - Replaced by `--expr "verify primesum(7,2) == 666"`
  - Or use `--equation verify-stf10` for the classic verification

### Technical Notes
- Grammar now supports optional quantifier: `[quantifier] comparison`
- Auto-detection: no quantifier + no free variables → verify mode
- Error if no quantifier but expression has free variables
- Error if `verify` used with free variables

### Related Issues
- Issue #34: Add 'verify' quantifier for closed-formula evaluation (complete)
- Issue #32: VSCode debug configuration (complete)

### Design Documents
- `2026-02-05__02-08-55__verify-quantifier-and-vscode-config.md`

## [0.7.5] - 2026-02-04

### Added
- **Multi-algorithm sieve system** (Issue #29)
  - Strategy Pattern: `_python_sieve()` facade dispatches to specialized implementations
  - `_basic_sieve()`: Original O(n) memory implementation
  - `_segmented_sieve()`: O(√n + segment) bounded memory for large ranges
  - `_individual_sieve()`: O(primes found) minimal memory fallback
  - Auto-selection based on available system memory
- **CLI algorithm flags**
  - `--algorithm sieve:<variant>` - Force specific algorithm (auto/primesieve/basic/segmented/individual)
  - `--prefer [cpu|gpu|memory|minimal]` - Resource preference hint
  - `--max-memory MB` - Set memory limit for sieve operations
  - `--list-algorithms` - Display available algorithm variants with complexity info
- **config.json algorithm settings**
  - `algorithms.sieve` - Default sieve algorithm
  - `max_memory_mb` - Default memory limit
  - `prefer` - Default resource preference
  - Three-tier precedence: CLI > config.json > auto-detection
- `config.json.example` - Sample configuration with documented options
- `--show-config` now displays algorithm settings
- 39 new tests (34 sieve + 5 config) - 355 total tests passing

### Technical Notes
- Segmented sieve uses same O(n log log n) complexity as basic sieve
- Memory bounded to segment_size + √limit primes cache
- Segment size defaults to 10% of available memory (1MB-100MB bounds)
- `psutil` optional for memory detection (falls back to 1GB default)

### Related Issues
- Issue #29: Segmented sieve with memory bounds (complete)
- Issue #30: Algorithm Variant System (foundation laid)
- Issue #12: Pre-filter benchmark (informed individual sieve)

### Design Documents
- `2026-02-04__19-49-53__segmented-sieve-memory-bounded.md`
- `2026-02-04__20-34-47__sieve-implementation-tradeoffs.md`

## [0.7.4] - 2026-02-04

### Added
- **Conda environment file** `environment.yml` for reproducible setup
  - Includes all dependencies: python-primesieve, numpy, pytest, cupy, lark
  - Configured for Python 3.10 (required for primesieve on Windows)
- Primesieve Python bindings now working (125M primes/sec benchmark)

### Changed
- Updated `docs/install.md` with comprehensive conda installation guide
- Updated `README.md` to reference environment.yml and Python 3.10 requirement
- Fixed Unicode encoding issue in benchmark script (arrow character)

### Fixed
- Issue #28: Primesieve environment now properly configured
- Venv backed up to `private/backup/` to avoid confusion with conda

### Technical Notes
- Windows requires Python 3.10 for primesieve (conda-forge limitation)
- Use `python-primesieve` package (not `primesieve` which is C++ library only)
- Benchmark confirms primesieve throughput: ~125M primes/sec at 1M range

### Reopened
- Issue #7: Can now run actual GPU vs primesieve benchmark (was theoretical only)

## [0.7.3] - 2026-02-04

### Added
- **Saved Equation System** `equations.json` (Issue #21)
  - Load equations by ID or name: `--equation 1` or `--equation primesum-squared`
  - `--list-equations` - List all available saved equations
  - `--var` flag for parameter substitution: `--var a=3` or `--var a=3,b=4`
  - Support for `default: true` marker in equations
  - Three-tier default precedence: config.json > equations.json > hardcoded
- **Configuration System** `config.json` (Issue #22)
  - `--show-config` - Display effective configuration and default equation
  - `default_equation` field to override equations.json default
  - `default_bounds` field for custom variable bounds
- Default `equations.json` shipped with 4 built-in equations:
  - `primesum-squared` (default) - Sum of squared primes
  - `primesum-cubed` - Sum of cubed primes
  - `tri-match` - Prime sums vs triangular numbers
  - `fib-match` - Prime sums vs Fibonacci numbers
- `ParameterDef` dataclass for equation parameters with type hints
- `IteratorDef` dataclass placeholder for custom iterators (Issue #24)
- 17 new unit tests for equation loading and configuration

### Changed
- `utils/cli.py` implements full equation and config loading (was stubs)
- Total test count: 316 passing (was 299)

### Technical Notes
- Equation parameters support auto-type inference (int/float/str)
- Unknown --var parameters trigger warning but continue execution
- Equations use variable names (n, m) not CLI flags (max_n) for bounds

### Phase 2 Progress (Completed!)
This release completes Phase 2 of the Expression Grammar epic (#13):
- ✅ #17: Expression parser with AST
- ✅ #18: CLI rewrite with decomposed flags
- ✅ #21: Saved equations with equations.json
- ✅ #22: Default configuration with config.json
- ⏳ #24: Custom iterators (v0.7.4)
- ⏳ #23: Smart early termination (v0.7.5)

## [0.7.2] - 2026-02-04

### Added
- **CLI rewrite with decomposed flags** `utils/cli.py` (Issue #18)
  - `--expr` - Full expression syntax: `--expr "does_exist primesum(n,2) == 666"`
  - `--lhs` - Left-hand side expression (default: primesum(n,2))
  - `--rhs` / `--target` - Right-hand side value (required unless using --expr)
  - `--operator` / `--op` - Comparison operator (==, !=, <, >, <=, >=)
  - `--quantifier` / `-q` - Quantifier (does_exist, for_any)
  - `--format` - Output format (text, json, csv)
  - `--verbose` - Show detailed progress and timing
- `ExpressionComponents` dataclass for decomposed expression building
- Stubs for saved equations (Issue #21) and default configuration (Issue #22) - implemented in v0.7.3
- 29 new unit tests for CLI module (`tests/test_cli.py`)
- 22 new CLI integration tests (`tests/test_cli_integration.py`)

### Changed
- `prime-square-sum.py` rewritten to use expression-based evaluation
- Total test count: 299 passing (was 248)

### Technical Notes
- Four-tier CLI architecture: Full expressions → Decomposed flags → Saved equations → Default mode
- Override precedence: CLI flags > Saved equation defaults > Config defaults > Built-in defaults
- Built-in defaults: `--lhs primesum(n,2)`, `--operator ==`, `--quantifier does_exist`

### Phase 2 Progress
This release implements the CLI rewrite for Phase 2 of the Expression Grammar epic (#13):
- ✅ #17: Expression parser with AST
- ✅ #18: CLI rewrite with decomposed flags
- ✅ #21: Saved equations (implemented in v0.7.3)
- ✅ #22: Default configuration (implemented in v0.7.3)

## [0.7.1] - 2026-02-04

### Added
- **Expression parser with Lark** `utils/grammar.py` (Issue #17)
  - AST classes: `Literal`, `Variable`, `FunctionCall`, `Comparison`, `Expression`
  - `ExpressionParser` - Lark-based LALR parser for expression grammar
  - `ExpressionEvaluator` - Evaluates AST with FunctionRegistry integration
  - `find_free_variables()` - Detects unbound variables in expressions
  - `find_matches()` - Iteration engine for `does_exist`/`for_any` quantifiers
  - `ParseError`, `EvaluationError` - Friendly error messages
- 59 new unit tests for grammar module
- `lark>=1.1.0` dependency (available via pip and conda-forge)

### Changed
- Total test count: 248 passing (was 189)

### Technical Notes
- Parse-once, evaluate-many pattern for performance
- Supports nested function calls: `tri(qtri(666))`
- Two-variable iteration: `for_any primesum(n,2) == tri(m)`
- Hard error for missing variable bounds (scientific rigor)

### Phase 2 Progress
This release implements the parser core for Phase 2 of the Expression Grammar epic (#13):
- ✅ #17: Expression parser with AST (core complete)
- ⏳ #18: CLI rewrite with `--expr` (next)

## [0.7.0] - 2026-02-04

### Added
- **Triangular number functions** in `utils/number_theory.py` (Issue #14)
  - `tri(n)` - nth triangular number: tri(36) = 666
  - `qtri(x)` - inverse triangular: qtri(666) = 36
  - `trisum(b)` - row-sum of digit triangle: trisum(10) = 666
  - `is_triangular(x)` - check if value is triangular
- **FunctionRegistry plugin architecture** (Issue #15)
  - `FunctionRegistry` class with automatic built-in registration
  - `FunctionSignature` dataclass with metadata (arg_count, varargs, docstring)
  - `--list-functions` CLI flag to show available functions
  - `--functions <file.py>` CLI flag to load user-defined functions
  - Argument count validation for static analysis
- **Sequence generators module** `utils/sequences.py` (Issue #16)
  - `primesum(n, power)` - sum of first n primes^power: primesum(7, 2) = 666
  - `fibonacci(n)` - nth Fibonacci number
  - `factorial(n)` - n factorial
  - `catalan(n)` - nth Catalan number
  - `_ensure_int()` helper for numeric type coercion
- 100 new unit tests (19 triangular + 41 registry + 40 sequences)
- Issue #20 created for numeric type handling policy

### Changed
- FunctionRegistry now has 10 built-in functions (was 0, as it's new)
- Total test count: 189 passing (was 89)

### Technical Notes
- `primesum()` includes reserved `_cache` parameter for future optimization (Issue #19)
- Sequences accept integral floats (7.0 → 7) but reject non-integral (7.5 → error)
- Expert consultation with Gemini 2.5 Pro validated architecture decisions

### Phase 1 Complete
This release completes Phase 1 (Foundation) of the Expression Grammar epic (#13):
- ✅ #14: Triangular functions
- ✅ #15: FunctionRegistry plugin architecture
- ✅ #16: Sequence generators module

Next: Phase 2 - Lark parser and `--expr` CLI interface

## [0.6.0] - 2026-02-03

### Added
- **Incremental sum caching** via `IncrementalSumCache` class (Issue #5)
  - O(1) per prime vs O(n) batch recomputation
  - Multi-power tracking (p², p³, p⁴ simultaneously)
  - Persistent `.npz` checkpoints with arbitrary precision
  - Adaptive checkpointing intervals (1K→100→10→1 based on prime count)
- `--no-cache` CLI flag to disable caching (caching now default)
- `utils/sum_cache.py` - New caching infrastructure (~250 lines)
- `utils/number_theory.py` - Digital root utilities (Issue #8)
  - `digital_root()` - O(1) calculation via formula
  - `could_be_prime_by_digital_root()` - Filters multiples of 3
  - `could_be_prime()` - Combined filter (~66% candidate elimination)
- GPU sieving benchmark in `tests/one-offs/performance/benchmark_sieve.py` (Issue #7)
- Windows primesieve installation guide in `docs/install.md` (Issue #3)
- 43 new unit tests (16 integration + 27 number theory)

### Fixed
- Cache "power not in cache" handler no longer destroys existing data
- JSON serialization for numpy int64 types from primesieve
- `last_prime` initialization changed from 0 to None (semantic correctness)
- Docstring error: `digital_root(666)` returns 9, not 3

### Changed
- Caching enabled by default (use `--no-cache` to disable)
- Improved primesieve warning with conda installation instructions

### Performance
- Incremental caching: 5x+ speedup for repeated target searches
- Checkpoint I/O: ~10ms (negligible overhead)
- Multi-power sums computed in single pass

### Closed Issues
- #2: Arbitrary prime powers (completed in v0.5.1, commit 3a39c61)
- #3: Windows primesieve installation guide
- #5: Incremental sum caching with checkpointing
- #7: GPU sieving evaluation (primesieve remains optimal)
- #8: Digital root utility for primality pre-filtering

### Deferred to v0.7.x
- #1: Distributed computing (open)
- #6: OEIS-style sequence storage
- #9-12: Cache architecture improvements (power-based isolation)

## [0.5.2] - 2026-02-02

### Added
- Hybrid GPU/CPU approach for higher powers (Issue #4)
- `gpu_power_values()` function for GPU exponentiation with CPU summing
- `_find_int64_cutoff_index()` for finding int64 boundary in prime arrays
- 6 new tests for hybrid approach (26 total)

### Changed
- `power_sum()` now uses hybrid approach: GPU for primes where p^n fits in int64, CPU for the rest
- power=3 with 1M primes now uses ~15% GPU acceleration instead of pure CPU
- Test coverage expanded from 20 to 26 tests

## [0.5.1] - 2026-02-02

### Added
- GPU acceleration via CuPy for sum of squared primes (5x speedup)
- `utils/gpu.py` module with `gpu_power_sum()`, `cpu_power_sum()`, `power_sum()`
- Adaptive chunk sizing to prevent int64 overflow on GPU
- Automatic CPU fallback when GPU would overflow (power > 2 with large primes)
- `--power` CLI argument for arbitrary prime powers (Σp^n)
- `--no-gpu` CLI argument to force CPU computation
- `requirements.txt` with numpy and cupy-cuda12x
- `run_tests.py` test driver script
- `tests/test_gpu.py` with 20 unit tests
- `tests/one-offs/performance/benchmark_gpu.py` for benchmarking

### Changed
- primesieve warning now shows once per session (not on every import)
- Silence warning via `PRIME_SQUARE_SUM_QUIET=1` environment variable

## [0.5.0] - 2026-02-02

### Added
- Python 3 migration with modern idioms
- NumPy integration for faster prime loading
- Multiprocessing support for parallel computation
- primesieve integration (optional)
- Checkpointing for resumable computations
- `utils/` module with `sieve.py` and `prime_io.py`
- Formal proofs in Lean 4 (`proofs/`)
- Verification scripts (`verification/`)

### Changed
- Prime file format from Pickle to NumPy (25x faster loading)
- Sieve algorithm from O(n²) to O(n log log n)
- License clarified to CC BY-NC-ND 4.0

## [0.1.0] - 2010

### Added
- Original Python 2 implementation
- Pickle-based prime storage
- Basic sieve of Eratosthenes
- Mathematica notebook with analysis
