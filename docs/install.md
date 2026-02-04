# Installation Guide

The [main README](../README.md) recommends **conda** as the primary installation method for simplicity and cross-platform compatibility. This guide covers all installation pathways, alternative approaches, troubleshooting, and GPU setup.

## Quick Start (Recommended)

Use the provided `environment.yml`:

```bash
# Install Anaconda or Miniconda first (see https://docs.anaconda.com/anaconda/install/)

# Create environment from file
conda env create -f environment.yml

# Activate
conda activate prime-square-sum

# Verify
python prime-square-sum.py --rhs 666
```

## Windows Users: Important Note

**Python 3.10 is required** for primesieve on Windows. The `python-primesieve` package in conda-forge only has Windows builds up to Python 3.10. The `environment.yml` file is configured for Python 3.10 to ensure primesieve works.

If you need Python 3.12+ for other reasons, you can:
1. Accept the pure Python fallback (slower but functional)
2. Use a separate Python 3.10 environment just for primesieve benchmarks

## Conda Manual Installation

If you prefer to install manually instead of using `environment.yml`:

```bash
# Create environment with explicit dependencies
conda create -n prime-square-sum python=3.10

# Activate
conda activate prime-square-sum

# Install dependencies from conda-forge
conda install -c conda-forge python-primesieve numpy pytest cupy lark

# Note: Use 'python-primesieve' not 'primesieve' - the latter is just the C++ library
```

## Python venv (Linux/Mac Only)

If you prefer the built-in Python virtual environment:

```bash
# Create virtual environment
python -m venv venv

# Activate (Linux/Mac)
source venv/bin/activate

# Install dependencies
pip install -r requirements.txt
```

**Windows Limitation:** `pip install primesieve` fails on Windows because it requires C++ compilation. On Windows, use conda instead.

**When to use venv:**
- You're on Linux/Mac where `pip install primesieve` works
- You want minimal environment overhead
- You don't need GPU acceleration

## Pure Python (No Optional Dependencies)

Minimal installation with just NumPy:

```bash
python -m venv venv
source venv/bin/activate  # or venv\Scripts\activate on Windows
pip install numpy lark
```

**Trade-offs:**
- ✅ Minimal dependencies, fast installation
- ❌ No primesieve (slower prime generation)
- ❌ No GPU acceleration (no CuPy)

**When to use:**
- You're using pre-computed primes from `data/npy_files/` (typical case)
- You don't have an NVIDIA GPU
- You want the smallest footprint

## Mamba (Faster Conda Alternative)

If you have `mamba` installed (faster dependency resolver):

```bash
mamba env create -f environment.yml
mamba activate prime-square-sum
```

Or manually:
```bash
mamba create -n prime-square-sum python=3.10
mamba install -c conda-forge python-primesieve numpy pytest cupy lark
```

## Docker (Containerized)

For reproducible environments across machines:

```dockerfile
FROM continuumio/miniconda3:latest

WORKDIR /app
COPY . /app

RUN conda env create -f environment.yml
RUN echo "conda activate prime-square-sum" >> ~/.bashrc
SHELL ["/bin/bash", "--login", "-c"]

CMD ["python", "prime-square-sum.py", "--rhs", "666"]
```

Build and run:
```bash
docker build -t prime-square-sum .
docker run prime-square-sum
```

## Handling primesieve on Windows

### Problem
`pip install primesieve` fails on Windows because it requires C++ compilation and the build environment is complex to set up.

### Solutions (in order of preference)

**1. Use Conda with Python 3.10 (Recommended)**
```bash
conda create -n prime-square-sum python=3.10
conda activate prime-square-sum
conda install -c conda-forge python-primesieve
```
Pre-compiled binary, works immediately.

**2. Accept Python Fallback**
The project automatically falls back to pure Python sieve if primesieve is unavailable. The warning message is non-fatal:

```bash
set PRIME_SQUARE_SUM_QUIET=1     # Windows CMD
$env:PRIME_SQUARE_SUM_QUIET=1    # PowerShell
```

To suppress the warning and see only the computation output.

**3. Build from Source (Advanced)**
If you need Python 3.11+ and want primesieve:

1. Install Visual Studio 2022 Build Tools with C++ workload
2. Install CMake
3. Clone and build primesieve C++ library
4. Set `CMAKE_PREFIX_PATH` to point to the build
5. `pip install primesieve`

This is complex and not recommended for most users.

## Verifying Installation

Regardless of installation method, verify everything works:

```bash
# Quick verification
python prime-square-sum.py --rhs 666

# Check GPU availability (if installed)
python -c "from utils.gpu import init_gpu, print_gpu_status; init_gpu(); print_gpu_status()"

# Check primesieve availability
python -c "from utils.sieve import PRIMESIEVE_AVAILABLE; print(f'primesieve: {\"Available\" if PRIMESIEVE_AVAILABLE else \"Not available (using fallback)\"}')"

# Run tests
pytest tests/ -q
```

## GPU Acceleration Setup

### NVIDIA GPU (CuPy)

If you have an NVIDIA GPU and want GPU acceleration:

**Requirements:**
- NVIDIA GPU (compute capability 3.0+)
- CUDA 12.x installed
- NVIDIA driver up to date

**Installation:**
```bash
# With conda (recommended - included in environment.yml)
conda install -c conda-forge cupy

# With pip (requires CUDA installed first)
pip install cupy-cuda12x
```

**Verify GPU setup:**
```bash
python -c "from utils.gpu import init_gpu, print_gpu_status; init_gpu(); print_gpu_status()"
```

### AMD GPU or No GPU

Pure CPU computation works fine. The project includes CPU-optimized algorithms:
- NumPy array operations (SIMD-friendly)
- Multiprocessing for parallel computation
- Incremental sum caching (v0.6.0+)

## Troubleshooting Installation

### ImportError: No module named 'numpy' or 'lark'
Make sure your environment is activated:
```bash
# Conda
conda activate prime-square-sum

# venv
source venv/bin/activate  # Linux/Mac
venv\Scripts\activate     # Windows
```

### primesieve import fails with "cannot open include file"
This is expected on Windows with pip. Use conda with Python 3.10 instead.

### "No module named 'primesieve'" with conda
Make sure you installed `python-primesieve` (the Python bindings), not just `primesieve` (the C++ library):
```bash
conda install -c conda-forge python-primesieve
```

### CuPy installation fails
- Check CUDA 12.x is installed: `nvidia-smi`
- Check CUDA toolkit: `nvcc --version`
- Use conda (easier): `conda install -c conda-forge cupy`

### Python version mismatch
If you see "python-primesieve not found", check your Python version:
```bash
python --version
```
On Windows, primesieve requires Python 3.10 (not 3.11 or 3.12).

## Requirements Files

| File | Purpose |
|------|---------|
| `environment.yml` | Conda environment (recommended) |
| `requirements.txt` | pip dependencies (Linux/Mac) |

## Recommendations by Scenario

| Scenario | Recommendation |
|----------|---|
| First-time user | **Conda + environment.yml** (simplest) |
| Windows user | **Conda + Python 3.10** (required for primesieve) |
| Linux/Mac developer | **venv** or **Conda** (both work) |
| GPU acceleration | **Conda** (CuPy pre-built) |
| Minimal footprint | **venv + pure Python** (no primesieve/CuPy) |
| Reproducible builds | **Docker** or **Conda + environment.yml** |
| Enterprise/CI/CD | **Docker** |

---

**Questions?** See [README.md](../README.md) for usage examples.
