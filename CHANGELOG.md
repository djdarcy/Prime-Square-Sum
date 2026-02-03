# Changelog

All notable changes to this project will be documented in this file.

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
