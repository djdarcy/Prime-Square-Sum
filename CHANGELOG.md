# Changelog

All notable changes to this project will be documented in this file.

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
