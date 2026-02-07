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

### Arithmetic Operators (v0.7.12+)

Expressions support standard arithmetic operators with Python-style precedence:

```bash
# Arithmetic in expressions
--expr "does_exist n**2 == 25"                          # n=5
--expr "verify 2 + 3 * 4 == 14"                         # true (precedence)
--expr "verify (2 + 3) * 4 == 20"                       # true (parens)
--expr "does_exist tri(n) + 1 == 11" --max-n 10         # n=4
--expr "does_exist primesum(n,2) - 1 == 665" --max-n 10 # n=7
```

#### Operator Precedence (highest to lowest)

| Precedence | Operators | Associativity | Example |
|------------|-----------|---------------|---------|
| 1 (highest) | Function calls, `(expr)` | N/A | `tri(n)`, `(2+3)` |
| 2 | `**` | Right | `2**3**2` = `2**(3**2)` = 512 |
| 3 | unary `-`, `+` | Right (prefix) | `-3`, `+x` |
| 4 | `*`, `/`, `//`, `%` | Left | `2 * 3 / 4` |
| 5 | `+`, `-` | Left | `1 + 2 - 3` |
| 6 (lowest) | `==`, `!=`, `<`, `>`, `<=`, `>=` | N/A | `n == 5` |

#### Arithmetic Operators

| Operator | Operation | Example | Result |
|----------|-----------|---------|--------|
| `+` | Addition | `2 + 3` | `5` |
| `-` | Subtraction | `10 - 4` | `6` |
| `*` | Multiplication | `3 * 7` | `21` |
| `/` | True division | `7 / 2` | `3.5` |
| `//` | Floor division | `7 // 2` | `3` |
| `%` | Modulo | `7 % 3` | `1` |
| `**` | Exponentiation | `2 ** 10` | `1024` |
| `-x` | Unary negation | `-5` | `-5` |
| `+x` | Unary positive | `+5` | `5` |

#### Behavioral Notes

- **`-3**2` equals `-9`**: Exponentiation binds tighter than unary minus (Python convention). Use `(-3)**2` for 9.
- **`2**3**2` equals `512`**: Right-associative — evaluated as `2**(3**2)` = `2**9`.
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
| Chained comparisons (`1 < x < 10`) | Use separate expressions |
| Boolean operators (`and`, `or`, `not`) | Future work — use separate expressions |
| Bitwise operators (`&`, `\|`, `^`, `~`) | Future work — create user functions |
| Complex numbers (`3+2j`) | Future work — use `complex(a, b)` function |
| Assignment (`x = 3 + 2`) | Use `--equation` with parameters |

## See Also

- [equations.md](equations.md) - Saved equations and `equations.json`
- [functions.md](functions.md) - Function reference and custom functions
