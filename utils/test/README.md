# Test Utilities

Legacy test code and utilities from the original 2010 implementation.

## Files

### bitset.py
A Python bitset implementation for memory-efficient prime sieves.

**Features:**
- Sequence-like interface for bit manipulation
- Supports bitwise operations (AND, OR, XOR, NOT)
- Left/right shift operations
- Slice notation for getting/setting ranges

**Potential use:** Memory-efficient Sieve of Eratosthenes where each bit represents a number's primality status.

### bitset_test.py
Unit tests for the bitset implementation.

### recipe-576738-1.py
Alternative bitset implementation from ActiveState Python recipes.

### long-test.py
Tests for Python's arbitrary precision integer handling.

### test-pickle.py
Tests for pickle serialization of prime lists, used to verify the `.dat` file format.

### prime-texttable-to-list.py
Converts prime number text files (8-column table format) into pickle `.dat` files. This is how the original `allmil.dat` (50M primes) was created in 2010.

**Usage (Python 2):**
```bash
python prime-texttable-to-list.py output.dat primes1.txt primes2.txt ...
```

**Note:** This is superseded by `utils/prime_io.py` which handles format conversions in Python 3.

## Status

These files are **legacy code** from 2010. They may be useful as reference for:
- Understanding the original implementation approach
- Memory-efficient sieve implementations
- Pickle format compatibility

The current implementation (`prime-square-sum.py`) uses NumPy arrays instead of custom bitsets, which provides better performance through C-optimized operations.

## Usage

```bash
# Run bitset tests
python bitset_test.py

# Test pickle format
python test-pickle.py
```
