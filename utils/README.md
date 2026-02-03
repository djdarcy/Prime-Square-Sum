# Utilities

Core utility modules for the optimized Prime-Square-Sum calculator.

## Modules

### sieve.py
Prime number generation using the Sieve of Eratosthenes.

**Features:**
- Wraps `primesieve` library (fastest known implementation) when available
- Falls back to pure Python NumPy-based sieve if primesieve unavailable
- Functions: `generate_primes()`, `generate_n_primes()`, `nth_prime()`, `prime_count()`

**Installation for best performance:**
```bash
# Linux/Mac
pip install primesieve

# Windows (recommended)
conda install -c conda-forge primesieve
```

### prime_io.py
Prime number file I/O with multiple format support.

**Supported formats:**
| Extension | Format | Speed | Size |
|-----------|--------|-------|------|
| `.npy` | NumPy binary | Fastest (25x) | Larger |
| `.npz` | NumPy compressed | Fast | Smaller |
| `.pkl`, `.dat` | Python pickle | Slow | Medium |
| `.txt`, `.csv` | Plain text | Slowest | Largest |

**Features:**
- Auto-detection of file format
- Memory-mapped loading for large files (`.npy`)
- Backward compatible with legacy `.dat` pickle files
- Range loading for partial file access

**Usage:**
```python
from utils import load_primes, save_primes, generate_n_primes

# Load from any format
primes = load_primes("primes.npy")
primes = load_primes("legacy.dat")  # pickle format

# Save in numpy format (recommended)
save_primes(primes, "output.npy")

# Generate and save
primes = generate_n_primes(1_000_000)
save_primes(primes, "first_million.npy")
```

### test/
Legacy test utilities from the 2010 implementation (bitset, pickle tests). See `test/README.md` for details.

## Performance Comparison

Loading 50 million primes:
| Format | Load Time |
|--------|-----------|
| NumPy (.npy) | 0.15s |
| Pickle (.dat) | 3.81s |

**NumPy is 25x faster** for loading large prime datasets.

### gpu.py
GPU-accelerated computation using CuPy.

**Features:**
- CuPy-based GPU computation (NVIDIA CUDA)
- Automatic GPU detection and initialization
- Graceful fallback to CPU multiprocessing
- Support for arbitrary prime powers (Σp^n)
- Chunked processing for GPU memory management

**Installation:**
```bash
# CUDA 12.x
pip install cupy-cuda12x

# Or use conda
conda install -c conda-forge cupy
```

**Usage:**
```python
from utils import init_gpu, power_sum, GPU_AVAILABLE

# Initialize GPU (call once at startup)
if init_gpu():
    print("GPU available!")
else:
    print("Falling back to CPU")

# Compute sum of squared primes (GPU if available, else CPU)
primes = load_primes("data/npy_files/1stmil.npy")
result = power_sum(primes, power=2)  # Σp²

# Or explicitly use GPU
from utils import gpu_power_sum
result = gpu_power_sum(primes, power=3)  # Σp³ on GPU
```

**Performance:**
| Method | 50M primes | Notes |
|--------|------------|-------|
| Single-threaded CPU | ~60s | Baseline |
| Multiprocessing CPU | ~8s | 8 cores |
| GPU (RTX 5090) | <1s | 100x+ speedup |

## Common Workflows

### Generate and Save Primes

```python
from utils import generate_n_primes, save_primes

# Generate first N primes and save for later
primes = generate_n_primes(10_000_000)  # 10 million
save_primes(primes, "10mil.npy")

# Or generate all primes up to a limit
from utils.sieve import generate_primes
primes = generate_primes(1_000_000_000)  # all primes < 1 billion
save_primes(primes, "primes_under_1B.npy")
```

### Convert Legacy Pickle to NumPy

```python
from utils.prime_io import convert_pickle_to_numpy

# One-liner conversion
count = convert_pickle_to_numpy("legacy.dat", "modern.npy")
print(f"Converted {count:,} primes")

# Or manually for more control
from utils import load_primes, save_primes
primes = load_primes("legacy.dat")
save_primes(primes, "modern.npy")
```

### Save in Multiple Formats

```python
from utils import load_primes, save_primes

primes = load_primes("primes.npy")

# NumPy binary (fastest loading)
save_primes(primes, "primes.npy")

# Pickle (legacy compatibility)
save_primes(primes, "primes.dat", format='pkl')

# Text (human readable, portable)
save_primes(primes, "primes.txt")
```

### Memory-Efficient Range Loading

```python
from utils.prime_io import load_primes_range

# Load only primes 1M through 2M (zero-indexed)
# Uses memory-mapping for .npy files - doesn't load entire file
subset = load_primes_range("data/npy_files/allmil.npy", 1_000_000, 2_000_000)
```
