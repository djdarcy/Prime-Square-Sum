# Changelog

All notable changes to this project will be documented in this file.

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
