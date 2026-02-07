# Prime-Square-Sum

[![Version](https://img.shields.io/github/v/release/djdarcy/Prime-Square-Sum?label=version)](https://github.com/djdarcy/Prime-Square-Sum/releases)
[![Python](https://img.shields.io/badge/python-3.10+-green.svg)](https://www.python.org/)
[![License](https://img.shields.io/badge/license-CC%20BY--NC--ND%204.0-lightgrey.svg)](LICENSE)

📓 **[View the Mathematica Notebook](https://github.com/djdarcy/Prime-Square-Sum/blob/main/paper%20and%20notes/2010%20-%20Recurrence%20relation%20between%20triangular%20numbers%20and%20squared%20primes%20-%20D.%20Darcy.nb)** *(Requires [Mathematica](https://www.wolfram.com/mathematica/) or [Wolfram Player](https://www.wolfram.com/player/))*

The python program is a computational platform for validating mathematical relationships. It checks LHS expressions against RHS targets and stores sequences for future analysis. The main focus of `prime-square-sum` is on summing triangular row values together to determine if:

![stf(b) = sum_(z=1)^qg(b) tf(b,z);](<paper and notes/function-stf-defined.png> "stf defined")

is equal to the series of squared/cubed primes.

```
b = triangular number (also the number base);              //equal to: tri(r)=(r^2+r)/2
r = qg(b) = size of the base row of the triangular number; //qg(b) = 1/2(-1+sqrt(1+8b)
z = row in the triangular number;  //ex. tf(10,4)=0123; tf(10,3)=456; tf(10,2)=78, etc.)
```

Where `tf()` is defined to be:

![tf(b,z) = (-2 + 2b - 2b^2 + z - bz - z^2 + bz^2 + b^z(2 + 2b^2 + z + z^2 - b(2 + z + z^2))) / (2(-1 + b)^2)](<paper and notes/function-tf-defined.png> "tf defined")

There is an interesting relationship when `{b=10, r=4}` where the sum of the triangular rows in base-10, `0123 + 456 + 78 + 9`, happens to work out to be the sum of the first seven squared primes.

```
stf(10) = 2² + 3² + 5² + 7² + 11² + 13² + 17² = 666
```

What I find fascinating about this relationship is the resultant value 666 is a triangular number itself. So the question then is if we were able to sum the rows of a 666 element triangle with 36 rows in base-666 would the result _also_ be the sum of squared or cubed primes?

This program attempts to provide an answer. The base-10 number from `stf(666)` unfortunately though is massively large at 98 digits:

`37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290`

While `stf(b)` is a closed-form function, `primesum(n,p)` is computationally irreducible. This means there is no readily available formula to directly find which `n` satisfies `primesum(n,p) = stf(b)`. So, in the absence of a better method, we enumerate prime sums and check for matches. See [docs/rationale.md](docs/rationale.md) for additional details as to why this tool needs to be as flexible and versatile as it is.

Due to the huge size of the 98-digits I've further adapted `prime-square-sum` to work with multiprocessing and CUDA (via CuPy) to speed up the computations. See the Mathematica notebook in [`paper and notes/`](https://github.com/djdarcy/Prime-Square-Sum/tree/main/paper%20and%20notes) for more details.

## Usage

```bash
# Find n where sum of first n squared primes equals 666
python prime-square-sum.py --expr "does_exist primesum(n,2) == 666"
# Output: Found: n=7  (because 2² + 3² + 5² + 7² + 11² + 13² + 17² = 666)

# Shorthand using default expression
python prime-square-sum.py --target 666
```

The `--target` flag searches against the **default expression** `primesum(n,2)` (sum of squared primes). This default is defined in `equations.json` and can be customized via `config.json`. See [docs/equations.md](docs/equations.md) for details.

```bash
# Find matches between prime sums and triangular numbers
python prime-square-sum.py --expr "for_any primesum(n,2) == tri(m)" --max-n 100 --max-m 50

# List available functions
python prime-square-sum.py --list functions
```

### Arithmetic Expressions (v0.7.12+)

Use standard arithmetic operators directly in expressions:

```bash
# Arithmetic in expressions
python prime-square-sum.py --expr "does_exist n**2 == 25"                     # n=5
python prime-square-sum.py --expr "does_exist tri(n) + 1 == 11" --max-n 10    # n=4
python prime-square-sum.py --expr "verify (2 + 3) * 4 == 20"                  # true

# Operators: +  -  *  /  //  %  **  (unary: -x, +x)
# Python-compatible precedence and associativity
```

See [docs/expressions.md](docs/expressions.md) for the precedence table and behavioral notes.

### Verify Mode (v0.7.6+)

Verify known results without iteration using the `verify` quantifier:

```bash
# Explicit verify - returns true/false
python prime-square-sum.py --expr "verify primesum(7,2) == 666"  # Returns: true

# Implicit verify - auto-detected when no free variables
python prime-square-sum.py --expr "primesum(7,2) == trisum(10)"  # Returns: true

# Using saved equation
python prime-square-sum.py --equation verify-stf10

# JSON output for programmatic use
python prime-square-sum.py --expr "verify primesum(7,2) == trisum(10)" --format json
# Returns: {"verified": true}
```

The `verify` quantifier evaluates closed formulas (no free variables) directly, returning `true` or `false` without any iteration.

### Algorithm Selection (v0.7.5+)

Control which sieve algorithm is used for prime generation:

```bash
# List available algorithms
python prime-square-sum.py --list algorithms

# Force segmented sieve (bounded memory)
python prime-square-sum.py --target 666 --algorithm sieve:segmented

# Use minimal memory mode
python prime-square-sum.py --target trisum(10) --prefer minimal

# Set memory limit
python prime-square-sum.py --target trisum(10) --max-memory 512
```

Available algorithms: `auto`, `primesieve`, `basic`, `segmented`, `individual`

Settings can also be saved in `config.json` (see `config.json.example`).

## Installation

### Recommended: Conda

Use the provided `environment.yml` for easiest setup:

```bash
# Create environment from file
conda env create -f environment.yml
conda activate prime-square-sum

# Verify
python prime-square-sum.py --rhs 666
```

Or install manually:
```bash
conda create -n prime-square-sum python=3.10
conda activate prime-square-sum
conda install -c conda-forge python-primesieve numpy pytest cupy lark
```

**Note:** Windows requires Python 3.10 for primesieve (conda-forge builds only available up to 3.10).

This installs:
- `python-primesieve` - Fast prime generation (~125M primes/sec)
- `numpy` - Array operations
- `cupy` - GPU acceleration (requires NVIDIA GPU + CUDA)
- `lark` - Expression parser for `--expr` queries (v0.7.1+)

### Other Installation Methods

For venv, pip, Docker, GPU setup, and detailed troubleshooting, see [docs/install.md](docs/install.md).

## Documentation

| Document | Description |
|----------|-------------|
| [docs/rationale.md](docs/rationale.md) | Why this tool exists: computational irreducibility |
| [docs/expressions.md](docs/expressions.md) | Expression syntax, quantifiers, operators |
| [docs/equations.md](docs/equations.md) | Saved equations and `equations.json` format |
| [docs/functions.md](docs/functions.md) | Function reference and custom functions |
| [docs/install.md](docs/install.md) | Installation and setup guide |

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
