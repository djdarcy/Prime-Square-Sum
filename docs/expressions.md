# Expression System

The expression system allows you to query mathematical relationships using a domain-specific language.

## Quick Start

```bash
# Find n where sum of first n squared primes equals 666
python prime-square-sum.py --expr "does_exist primesum(n,2) == 666"
# Output: Found: n=7

# Verify a known result
python prime-square-sum.py --expr "verify primesum(7,2) == 666"
# Output: true

# Find all matches between two sequences
python prime-square-sum.py --expr "for_any primesum(n,2) == tri(m)" --max-n 100 --max-m 1000
# Output: Found: n=7, m=36
```

## Expression Syntax

An expression consists of an optional **quantifier** and a **comparison**:

```
[quantifier] left_side operator right_side
```

### Quantifiers

| Quantifier | Free Variables | Behavior | Use Case |
|------------|----------------|----------|----------|
| `does_exist` | Required | Find first match, stop | "Is there an n where...?" |
| `for_any` | Required | Find all matches | "What are all n,m where...?" |
| `verify` | None allowed | Evaluate directly | "Is this equation true?" |

**Examples:**
```bash
# does_exist - find first n where condition holds
--expr "does_exist primesum(n,2) == 666"

# for_any - enumerate all matching pairs
--expr "for_any primesum(n,2) == tri(m)"

# verify - check if a closed formula is true
--expr "verify primesum(7,2) == 666"
```

### Implicit Verify Mode

When you omit the quantifier and the expression has no free variables, `verify` mode is auto-detected:

```bash
# These are equivalent:
--expr "verify primesum(7,2) == 666"
--expr "primesum(7,2) == 666"
```

If you omit the quantifier but have free variables, you'll get a helpful error:
```
Error: Expression has free variables (n) but no quantifier.
Use 'does_exist' or 'for_any' prefix, e.g.: does_exist primesum(n,2) == 666
```

### Operator Precedence (v0.7.14+)

Full operator precedence from lowest to highest binding power:

| Level | Operators | Associativity | Type | Example |
|-------|-----------|---------------|------|---------|
| 1 (lowest) | `or`, `\|\|` | Left | Logical OR | `a or b` |
| 2 | `and`, `&&` | Left | Logical AND | `a and b` |
| 3 | `not`, `!` | Right (prefix) | Logical NOT | `not x` |
| 4 | `==`, `!=`, `<`, `>`, `<=`, `>=` | Chainable | Comparison | `1 < x < 10` |
| 5 | `bor`, `\|` | Left | Bitwise OR | `5 bor 3` |
| 6 | `xor` | Left | Bitwise XOR | `5 xor 3` |
| 7 | `band`, `&` | Left | Bitwise AND | `5 band 3` |
| 8 | `shl`/`<<`, `shr`/`>>` | Left | Bit shifts | `1 << 3` |
| 9 | `+`, `-` | Left | Addition | `2 + 3` |
| 10 | `*`, `/`, `//`, `%` | Left | Multiplication | `6 * 7` |
| 11 | `-x`, `+x`, `~`, `bnot` | Right (prefix) | Unary | `~0`, `-x` |
| 12 | `**`, `^` | Right | Exponentiation | `2^3` = 8 |
| 13 (highest) | Atoms, context blocks | N/A | Terminals | `tri(n)`, `bit[expr]` |

### Arithmetic Operators (v0.7.12+)

```bash
# Arithmetic in expressions
--expr "does_exist n**2 == 25"                          # n=5
--expr "verify 2 + 3 * 4 == 14"                         # true (precedence)
--expr "verify (2 + 3) * 4 == 20"                       # true (parens)
--expr "does_exist tri(n) + 1 == 11" --max-n 10         # n=4
--expr "does_exist primesum(n,2) - 1 == 665" --max-n 10 # n=7
```

| Operator | Operation | Example | Result |
|----------|-----------|---------|--------|
| `+` | Addition | `2 + 3` | `5` |
| `-` | Subtraction | `10 - 4` | `6` |
| `*` | Multiplication | `3 * 7` | `21` |
| `/` | True division | `7 / 2` | `3.5` |
| `//` | Floor division | `7 // 2` | `3` |
| `%` | Modulo | `7 % 3` | `1` |
| `**` | Exponentiation | `2 ** 10` | `1024` |
| `^` | Power alias | `2^3` | `8` |
| `-x` | Unary negation | `-5` | `-5` |
| `+x` | Unary positive | `+5` | `5` |

#### Behavioral Notes

- **`-3**2` equals `-9`**: Exponentiation binds tighter than unary minus (Python convention). Use `(-3)**2` for 9.
- **`2**3**2` equals `512`**: Right-associative — evaluated as `2**(3**2)` = `2**9`.
- **`2^3` equals `8`**: `^` is a power alias (math convention), same as `**`.
- **`7 / 2` equals `3.5`**: True division always returns float.
- **`7 // 2` equals `3`**: Floor division rounds toward negative infinity.
- **`0**0` equals `1`**: Python convention.
- **Division by zero**: Raises an error with a clear message.

#### Arithmetic in Function Arguments

Arithmetic expressions can be used inside function arguments:

```bash
--expr "verify pow(2 + 1, 2) == 9"       # pow(3, 2) = 9
--expr "does_exist primesum(n + 1, 2) == tri(m)"
```

### Boolean Operators (v0.7.14+)

Logical operators with short-circuit evaluation:

```bash
--expr "does_exist n > 0 and n < 10 and tri(n) == 28" --max-n 20   # n=7
--expr "verify 2 > 1 and 3 > 2"                                     # true
--expr "verify not 1 > 2"                                            # true
```

| Operator | Alias | Operation | Short-circuit |
|----------|-------|-----------|---------------|
| `and` | `&&` | Logical AND | Stops on first falsy |
| `or` | `\|\|` | Logical OR | Stops on first truthy |
| `not` | `!` | Logical NOT | N/A (unary) |

**Short-circuit behavior**: `0 and 1/0` does not raise an error (stops at `0`). `1 or 1/0` does not raise (stops at `1`).

### Bitwise Operators (v0.7.14+)

Integer bit manipulation operators, available as keywords or symbols:

```bash
--expr "verify 5 xor 3 == 6"       # 101 ^ 011 = 110
--expr "verify 5 band 3 == 1"      # 101 & 011 = 001
--expr "verify 5 bor 3 == 7"       # 101 | 011 = 111
--expr "verify ~0 == -1"           # bitwise NOT
--expr "verify 1 << 3 == 8"        # left shift
--expr "verify 8 >> 3 == 1"        # right shift
```

| Keyword | Symbol | Operation | Example |
|---------|--------|-----------|---------|
| `bor` | `\|` | Bitwise OR | `5 bor 3` = 7 |
| `xor` | — | Bitwise XOR | `5 xor 3` = 6 |
| `band` | `&` | Bitwise AND | `5 band 3` = 1 |
| `shl` | `<<` | Left shift | `1 shl 3` = 8 |
| `shr` | `>>` | Right shift | `8 shr 3` = 1 |
| `bnot` | `~` | Bitwise NOT (prefix) | `bnot 0` = -1 |

**Compound operations** (registered as functions):

| Function | Operation | Example |
|----------|-----------|---------|
| `nand(a, b)` | `~(a & b)` | `nand(5, 3)` = -2 |
| `nor(a, b)` | `~(a \| b)` | `nor(5, 3)` = -8 |
| `xnor(a, b)` | `~(a ^ b)` | `xnor(5, 3)` = -7 |

### Chained Comparisons (v0.7.14+)

Comparisons can be chained, Python-style:

```bash
--expr "verify 1 < 2 < 3"                                           # true
--expr "does_exist 1 < n < 10 and tri(n) == 28" --max-n 20          # n=7
--expr "verify 1 <= 2 < 3"                                          # true
```

`a < b < c` evaluates as `(a < b) and (b < c)` with `b` evaluated only once.

### Context Blocks (v0.7.14+)

Context blocks change how ambiguous operators are interpreted:

```bash
--expr "verify bit[2^3] == 1"          # ^ is XOR in bit context: 2 XOR 3 = 1
--expr "verify 2^3 == 8"               # ^ is power in default context
--expr "verify bit[5 or 3] == 7"       # or is bitwise OR in bit context
--expr "verify bit[5 and 3] == 1"      # and is bitwise AND in bit context
```

| Block | Effect |
|-------|--------|
| `num[expr]` | Numeric context (default — no-op) |
| `bit[expr]` | Bitwise context: `^`→XOR, `and`→bitwise AND, `or`→bitwise OR, `not`→bitwise NOT |
| `bool[expr]` | Explicit boolean context (same as default for `and`/`or`/`not`) |

**Mixed contexts**: Context blocks can appear anywhere in an expression:

```bash
--expr "verify bit[2^3] + 1 == 2"      # bit context for XOR, then addition in default context
--expr "verify bit[2 band 3 ^ 4] == 6" # ^ is XOR at correct precedence (level 6)
--expr "verify bit[2^3] + 2^3 == 9"    # first ^ is XOR (=1), second ^ is power (=8)
```

Inside `bit[...]`, `^` is parsed at XOR precedence (level 6, between bitwise OR and AND), matching Python/C/Mathematica operator precedence. The `**` operator is always exponentiation regardless of context.

### Comparison Operators

| Operator | Meaning |
|----------|---------|
| `==` | Equal to |
| `!=` | Not equal to |
| `<` | Less than |
| `>` | Greater than |
| `<=` | Less than or equal |
| `>=` | Greater than or equal |

### Functions

Use `--list functions` to see all available functions:

```bash
python prime-square-sum.py --list functions
```

Functions can be called with or without a namespace qualifier:

```bash
# Unqualified (resolved by priority: user > pss > math)
--expr "does_exist pow(n, 2) == tri(m)"

# Qualified (always resolves to specific namespace)
--expr "does_exist math.pow(n, 2) == pss.tri(m)"
```

Available namespaces: `pss` (tool-specific), `math` (Python math module), `user` (from `--functions`). See [functions.md](functions.md) for details.

**PSS built-in functions:**

| Function | Description | Example |
|----------|-------------|---------|
| `primesum(n, power)` | Sum of first n primes^power | `primesum(7,2) = 666` |
| `tri(n)` | nth triangular number | `tri(36) = 666` |
| `qtri(x)` | Inverse triangular (or None) | `qtri(666) = 36` |
| `fibonacci(n)` | nth Fibonacci number | `fibonacci(10) = 55` |
| `factorial(n)` | n! | `factorial(5) = 120` |
| `catalan(n)` | nth Catalan number | `catalan(5) = 42` |
| `digital_root(x)` | Digital root | `digital_root(666) = 9` |
| `complex(real, imag)` | Create complex number | `complex(3, 4)` = 3+4j |
| `real(z)` | Real part of complex | `real(complex(3, 4))` = 3 |
| `imag(z)` | Imaginary part of complex | `imag(complex(3, 4))` = 4 |
| `conj(z)` | Complex conjugate | `conj(complex(3, 4))` = 3-4j |

**Math functions** (all Python `math` module functions available via `math.*`):

### Variables and Bounds

Free variables (like `n`, `m`) are iterated over search ranges:

```bash
# Set bounds for variables (legacy syntax)
--expr "for_any primesum(n,2) == tri(m)" --max-n 1000 --max-m 5000
```

Default bounds:
- `--max-n`: 1,000,000
- `--max-m`: 10,000

### Iterator Syntax (v0.7.7+)

For more control over iteration, use `--iter-var`:

```bash
# Compact syntax: VAR:START:STOP[:STEP][:DTYPE]
--iter-var n:1:1000              # n from 1 to 1000, step 1
--iter-var n:1:100:2             # n = 1, 3, 5, ..., 99 (odd numbers)
--iter-var n:1:1000000:1:uint64  # Ensure primesieve compatibility

# Multiple variables
--expr "for_any primesum(n,2) == tri(m)" --iter-var n:1:100 --iter-var m:1:50
```

#### Iterator Flags

| Flag | Description | Example |
|------|-------------|---------|
| `--iter-var` | Compact iterator definition | `n:1:1000:2` |
| `--iter-type` | Variable type (int/float) | `--iter-type n:float` |
| `--iter-start` | Start value | `--iter-start n:1` |
| `--iter-stop` | Stop value (inclusive) | `--iter-stop n:1000` |
| `--iter-step` | Step size | `--iter-step n:2` |
| `--iter-num-steps` | Number of steps (linspace) | `--iter-num-steps x:11` |
| `--iter-dtype` | Data type constraint | `--iter-dtype n:uint64` |

#### Data Types

| dtype | Range | Use Case |
|-------|-------|----------|
| `int` | Arbitrary precision | Default, general use |
| `int32` | -2³¹ to 2³¹-1 | cupy GPU arrays |
| `int64` | -2⁶³ to 2⁶³-1 | cupy GPU arrays |
| `uint64` | 0 to 2⁶⁴-1 | primesieve compatibility |
| `float32` | ±3.4e38 | GPU floats |
| `float64` | ±1.8e308 | Standard floats |

#### Float Iteration

Float iteration uses Decimal precision to avoid accumulation errors:

```bash
# Float iteration with step
--iter-var x:0.0:1.0:0.1 --iter-type x:float

# Linspace-style (11 points from 0 to 1)
--iter-var x:0.0:1.0 --iter-type x:float --iter-num-steps x:11
```

## Decomposed Flags

For simpler queries, you can use decomposed flags instead of `--expr`:

| Flag | Purpose | Default |
|------|---------|---------|
| `--lhs` | Left-hand side expression | `primesum(n,2)` |
| `--rhs` / `--target` | Right-hand side value | (required) |
| `--operator` / `--op` | Comparison operator | `==` |
| `--quantifier` / `-q` | Quantifier | `does_exist` |

**Examples:**
```bash
# These are equivalent:
--expr "does_exist primesum(n,2) == 666"
--target 666

# Custom left-hand side:
--lhs "tri(n)" --target 666 --max-n 100
# Finds: n=36

# Different operator:
--lhs "primesum(n,2)" --operator ">=" --target 600 --max-n 10
# Finds first n where primesum(n,2) >= 600
```

## Output Formats

```bash
--format text   # Human-readable (default)
--format json   # JSON output
--format csv    # CSV output
```

**Examples:**
```bash
# Text output (default)
python prime-square-sum.py --target 666
# Found: n=7

# JSON output
python prime-square-sum.py --target 666 --format json
# {"found": true, "variables": {"n": 7}}

# Verify with JSON
python prime-square-sum.py --expr "verify primesum(7,2) == 666" --format json
# {"verified": true}
```

## Verbose Mode

Add `--verbose` for detailed output including timing and parsed expression:

```bash
python prime-square-sum.py --target 666 --verbose
# Expression: does_exist primesum(n,2) == 666
# Searching n in range [1, 1000000]...
# Found: n=7
# Time: 0.023s
```

## Expression Validation

Expressions are validated before evaluation (v0.7.12+). The parser checks:

1. **Syntax**: Malformed expressions produce parse errors with position indicators
2. **Functions**: Unknown function names are caught before iteration begins
3. **Arity**: Wrong number of arguments produces a clear error

```bash
# Unknown function caught at validation time
python prime-square-sum.py --expr "does_exist bogus(n) == 5"
# Error: Unknown function: 'bogus'

# Arity mismatch caught at validation time
python prime-square-sum.py --expr "verify tri(1, 2, 3) == 5"
# Error: tri() requires 1 argument(s), got 3
```

## Current Limitations

These features are not currently supported in the expression grammar. Most can be worked around using user-defined functions via `--functions` or saved equations in `equations.json`.

| Feature | Workaround |
|---------|-----------|
| Implicit multiplication (`2x`) | Write `2 * x` |
| Scientific notation (`1.5e10`) | Use `1.5 * pow(10, 10)` |
| Leading-dot decimals (`.5`) | Write `0.5` |
| Assignment (`x = 3 + 2`) | Use `--equation` with parameters |
| `xor` as variable name | Reserved — use a different name |

## Imaginary Literals (Opt-in)

Complex numbers can optionally be written using imaginary literal notation (v0.7.19+). This feature is **disabled by default** — use `complex()` for complex number creation without configuration.

To enable, set `imaginary_unit` in `config.json`:

```json
{ "imaginary_unit": "ii" }
```

Then use imaginary literals in expressions:

```bash
python prime-square-sum.py --expr "verify abs(3 + 4ii) == 5"        # magnitude
python prime-square-sum.py --expr "verify 1ii ** 2 == -1"           # i^2 = -1
python prime-square-sum.py --expr "verify real(3 + 4ii) == 3"
```

### Suffix options

| Value | Suffix | Example | Notes |
|-------|--------|---------|-------|
| `"none"` (default) | *(disabled)* | Use `complex(3, 2)` | All letters available as variables |
| `"ii"` | `ii` | `3 + 2ii` | Safe — `i`, `j` remain variables |
| `"i"` | `i` | `3 + 2i` | Math convention — reserves `i` in `NUMBER+i` |
| `"j"` | `j` | `3 + 2j` | Python/EE convention — reserves `j` in `NUMBER+j` |
| `"both"` | `i` or `j` | `3 + 2i` or `3 + 2j` | Reserves both in `NUMBER+suffix` |

Imaginary literals require a leading digit: `2ii` is imaginary, but standalone `ii` is always a variable. The `complex()` function works regardless of this setting.

## See Also

- [equations.md](equations.md) - Saved equations and `equations.json`
- [functions.md](functions.md) - Function reference and custom functions
