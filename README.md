# Prime-Square-Sum

[![Version](https://img.shields.io/github/v/release/djdarcy/Prime-Square-Sum?label=version)](https://github.com/djdarcy/Prime-Square-Sum/releases)
[![Python](https://img.shields.io/badge/python-3.8+-green.svg)](https://www.python.org/)
[![License](https://img.shields.io/badge/license-CC%20BY--NC--ND%204.0-lightgrey.svg)](LICENSE)

📓 **[View the Mathematica Notebook](https://github.com/djdarcy/Prime-Square-Sum/blob/master/paper%20and%20notes/2010%20-%20Recurrence%20relation%20between%20triangular%20numbers%20and%20squared%20primes%20-%20D.%20Darcy.nb)** *(Requires [Mathematica](https://www.wolfram.com/mathematica/) or [Wolfram Player](https://www.wolfram.com/player/))*

The python program squares primes and sums them together to determine if:

![stf(b) = sum_(z=1)^qg(b) tf(b,z);](/paper%20and%20notes/function-stf-defined.png?raw=true "stf defined")

is equal to a series of squared primes.

```
b = triangular number (also the number base);              //equal to: (r^2+r)/2
r = qg(b) = size of the base row of the triangular number; //qg(b) = 1/2(-1+sqrt(1+8b)
z = row in the triangular number;  //ex. tf(10,4)=0123; tf(10,3)=456; tf(10,2)=78, etc.)
```

Where tf() is defined to be:

![tf(b,z) = (-2 + 2b - 2b^2 + z - bz - z^2 + bz^2 + b^z(2 + 2b^2 + z + z^2 - b(2 + z + z^2))) / (2(-1 + b)^2)](/paper%20and%20notes/function-tf-defined.png?raw=true "tf defined")

There is an interesting relationship when `{b=10, r=4}` where the sum of the triangular rows in base-10, `0123 + 456 + 78 + 9`, happens to work out to be the sum of the first seven squared primes.

```
stf(10) = 2² + 3² + 5² + 7² + 11² + 13² + 17² = 666
```

What I find fascinating about this relationship is the resultant value 666 is a triangular number itself. So the question then is if we were able to sum the rows of a 666 element triangle with 36 rows in base-666 would the result _also_ be the sum of squared or cubed primes?

This program attempts to provide an answer. The base-10 number from `stf(666)` is massively large unfortunately at 98 digits:

`37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290`

So I've adapted it to work with multiprocessing and CUDA (via CuPy) to speed up the computations. See the Mathematica notebook in [`paper and notes/`](https://github.com/djdarcy/Prime-Square-Sum/tree/master/paper%20and%20notes) for more details.

## Usage

```bash
# Verify stf(10) = 666
python prime-square-sum.py --verify-666

# Search with precomputed primes (download from Releases into data/)
python prime-square-sum.py --target 666 --prime-file data/npy_files/1stmil.npy

# Resume from checkpoint
python prime-square-sum.py --resume checkpoint.json
```

## Installation

### Quick Start (CPU only)
```bash
pip install numpy
```

### Full Setup with GPU Acceleration (Recommended)

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

The `requirements.txt` includes:
- `numpy` - Array operations
- `cupy-cuda12x` - GPU acceleration (requires NVIDIA GPU + CUDA 12.x)

### Optional: Faster Prime Generation

```bash
pip install primesieve  # Linux/Mac
conda install -c conda-forge primesieve  # Windows
```

### Verify GPU Setup

```bash
python -c "from utils.gpu import init_gpu, print_gpu_status; init_gpu(); print_gpu_status()"
```

## Precomputed Primes

Large prime datasets available via [GitHub Releases](https://github.com/djdarcy/Prime-Square-Sum/releases):

| File | Primes | Format |
|------|--------|--------|
| `1stmil.npy` | 1M | NumPy |
| `allmil.npy` | 50M | NumPy |
| `*.dat` | legacy | Pickle |

## Project Structure

```
Prime-Square-Sum/
├── prime-square-sum.py      # Main program
├── run_tests.py             # Test runner
├── utils/                   # Sieve, I/O, GPU utilities
├── tests/                   # Unit tests
├── proofs/                  # Lean 4 proofs
├── verification/            # Verification scripts
├── paper and notes/         # Mathematica notebook
└── data/                    # Prime files (download from Releases)
    ├── npy_files/           # NumPy format (recommended)
    └── dat_files/           # Pickle format (legacy)
```

## Roadmap

- [x] GPU acceleration (CuPy) - v0.5.1
- [ ] Distributed computing
- [ ] Alternative primality testing

See [Issue #1](https://github.com/djdarcy/Prime-Square-Sum/issues/1) for details.

## Related

See [Zero_AG to The Scarcity Framework](https://github.com/Way-of-Scarcity/papers) for related theoretical work.

## Contributing

Pull requests welcome. Start a conversation in [Discussions](https://github.com/djdarcy/Prime-Square-Sum/discussions).

[!["Buy Me A Coffee"](https://www.buymeacoffee.com/assets/img/custom_images/orange_img.png)](https://www.buymeacoffee.com/djdarcy)

## License

prime-square-sum, Copyright (C) 2010 to 2026 Dustin Darcy. This work is licensed under [CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/) (Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International).

- **Attribution**: You must give appropriate credit when referencing this work
- **NonCommercial**: You may not use this for commercial purposes
- **NoDerivatives**: You may not distribute modified versions without permission

See [LICENSE](LICENSE) for full details.
