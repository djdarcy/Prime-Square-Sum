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

### Operators

| Operator | Meaning |
|----------|---------|
| `==` | Equal to |
| `!=` | Not equal to |
| `<` | Less than |
| `>` | Greater than |
| `<=` | Less than or equal |
| `>=` | Greater than or equal |

### Functions

Use `--list-functions` to see all available functions:

```bash
python prime-square-sum.py --list-functions
```

**Built-in functions:**

| Function | Description | Example |
|----------|-------------|---------|
| `primesum(n, power)` | Sum of first n primes^power | `primesum(7,2) = 666` |
| `tri(n)` | nth triangular number | `tri(36) = 666` |
| `qtri(x)` | Inverse triangular (or None) | `qtri(666) = 36` |
| `fibonacci(n)` | nth Fibonacci number | `fibonacci(10) = 55` |
| `factorial(n)` | n! | `factorial(5) = 120` |
| `catalan(n)` | nth Catalan number | `catalan(5) = 42` |
| `digital_root(x)` | Digital root | `digital_root(666) = 9` |

### Variables and Bounds

Free variables (like `n`, `m`) are iterated over search ranges:

```bash
# Set bounds for variables
--expr "for_any primesum(n,2) == tri(m)" --max-n 1000 --max-m 5000
```

Default bounds:
- `--max-n`: 1,000,000
- `--max-m`: 10,000

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

## See Also

- [equations.md](equations.md) - Saved equations and `equations.json`
- [functions.md](functions.md) - Function reference and custom functions
