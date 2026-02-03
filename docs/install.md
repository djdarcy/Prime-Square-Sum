# Installation Guide

The [main README](../README.md) recommends **conda** as the primary installation method for simplicity and cross-platform compatibility. This guide covers all installation pathways, alternative approaches, troubleshooting, and GPU setup.

## Python venv (Standard Python)

If you prefer the built-in Python virtual environment:

```bash
# Create virtual environment
python -m venv venv

# Activate (Windows)
venv\Scripts\activate

# Activate (Linux/Mac)
source venv/bin/activate

# Install dependencies
pip install -r requirements.txt
```

**Limitations:**
- `primesieve` installation fails on Windows (requires C++ build tools)
  - Workaround: Accept the pure Python fallback (see below)
  - Or: Install pre-built wheel from https://github.com/kimwalisch/primesieve/releases
  - Or: Switch to conda for this dependency only

**When to use venv:**
- You don't have conda installed
- You want minimal environment overhead
- You're on Linux/Mac where `pip install primesieve` works

## Pure Python (No Optional Dependencies)

Minimal installation with just NumPy:

```bash
python -m venv venv
source venv/bin/activate  # or venv\Scripts\activate on Windows
pip install numpy
```

**Trade-offs:**
- ✅ Minimal dependencies, fast installation
- ❌ No primesieve (slower prime generation)
- ❌ No GPU acceleration (no CuPy)

**When to use:**
- You're using pre-computed primes from `data/npy_files/` (typical case)
- You don't have an NVIDIA GPU
- You want the smallest footprint

## Conda (Explicit Channel Specification)

For detailed control over conda installation:

```bash
# Create environment with explicit dependencies
conda create -n prime-square-sum \
  -c conda-forge \
  python=3.12 \
  numpy \
  primesieve \
  cupy-cuda12x

conda activate prime-square-sum
```

## Mamba (Faster Conda Alternative)

If you have `mamba` installed (faster dependency resolver):

```bash
mamba create -n prime-square-sum \
  -c conda-forge \
  python=3.12 \
  numpy \
  primesieve \
  cupy-cuda12x

mamba activate prime-square-sum
```

## Docker (Containerized)

For reproducible environments across machines:

```dockerfile
FROM continuumio/miniconda3:latest

WORKDIR /app
COPY . /app

RUN conda install -c conda-forge \
    python=3.12 \
    numpy \
    primesieve \
    cupy-cuda12x

CMD ["python", "prime-square-sum.py", "--verify-666"]
```

Build and run:
```bash
docker build -t prime-square-sum .
docker run prime-square-sum
```

## Handling primesieve on Windows

### Problem
`pip install primesieve` fails on Windows because it requires C++ compilation and the build environment is missing.

### Solutions (in order of preference)

**1. Use Conda (Recommended)**
```bash
conda install -c conda-forge primesieve
```
Pre-compiled binary, works immediately.

**2. Accept Python Fallback**
The project automatically falls back to pure Python sieve if primesieve is unavailable. The warning message is non-fatal:

```bash
export PRIME_SQUARE_SUM_QUIET=1  # Linux/Mac
set PRIME_SQUARE_SUM_QUIET=1     # Windows CMD
```

To suppress the warning and see only the computation output.

**3. Install Pre-built Wheel**
Check https://github.com/kimwalisch/primesieve/releases for Windows wheels:

```bash
# Download appropriate .whl file, then:
pip install primesieve-*.whl
```

**4. Set Up C++ Build Tools (Advanced)**
Install Visual Studio Build Tools or MinGW, then:
```bash
pip install primesieve
```

## Verifying Installation

Regardless of installation method, verify everything works:

```bash
# Quick verification
python prime-square-sum.py --verify-666

# Check GPU availability (if installed)
python -c "from utils.gpu import init_gpu, print_gpu_status; init_gpu(); print_gpu_status()"

# Check primesieve availability
python -c "from utils.sieve import PRIMESIEVE_AVAILABLE; print(f'primesieve: {\"Available\" if PRIMESIEVE_AVAILABLE else \"Not available (using fallback)\"}')"
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
# With conda (recommended)
conda install -c conda-forge cupy-cuda12x

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

### ImportError: No module named 'numpy'
Make sure your environment is activated:
```bash
# Conda
conda activate prime-square-sum

# venv
source venv/bin/activate  # Linux/Mac
venv\Scripts\activate     # Windows
```

### primesieve import fails with "cannot open include file"
This is expected on Windows with pip. Use conda instead, or accept the Python fallback.

### CuPy installation fails
- Check CUDA 12.x is installed: `nvidia-smi`
- Check CUDA toolkit: `nvcc --version`
- Use conda (easier): `conda install -c conda-forge cupy-cuda12x`

### Requirements.txt vs environment.yml
- `requirements.txt` - For pip installation
- No `environment.yml` currently - Conda users can use the command from README

To create an `environment.yml` from current conda environment:
```bash
conda env export > environment.yml
```

## Recommendations by Scenario

| Scenario | Recommendation |
|----------|---|
| First-time user | **Conda** (simplest, pre-compiled) |
| Linux/Mac developer | **venv** (works well, lightweight) |
| Windows user | **Conda** (solves primesieve problem) |
| GPU acceleration | **Conda** (CuPy pre-built) |
| Minimal footprint | **venv + pure Python** (no primesieve/CuPy) |
| Reproducible builds | **Docker** or **Conda + environment.yml** |
| Enterprise/CI/CD | **Docker** |

---

**Questions?** See [README.md](../README.md) for usage examples.
