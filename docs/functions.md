# Functions Reference

Functions are the building blocks of expressions. Use `--list-functions` to see all available functions.

## Quick Reference

```bash
# List all functions with descriptions
python prime-square-sum.py --list-functions

# Load custom functions from a file
python prime-square-sum.py --functions my_funcs.py --expr "does_exist my_func(n) == 666"
```

## Built-in Functions

### Prime Functions

#### `primesum(n, power)`
Sum of the first n primes raised to a power.

| Parameter | Description |
|-----------|-------------|
| `n` | Number of primes to sum |
| `power` | Exponent (default: 2) |

**Examples:**
```
primesum(1, 2) = 4        # 2^2
primesum(2, 2) = 13       # 2^2 + 3^2
primesum(7, 2) = 666      # 2^2 + 3^2 + 5^2 + 7^2 + 11^2 + 13^2 + 17^2
primesum(2, 1) = 5        # 2 + 3
primesum(4, 3) = 503      # 2^3 + 3^3 + 5^3 + 7^3
```

**Note:** This is the core function for investigating stf(b) relationships.

### Triangular Functions

#### `tri(n)`
The nth triangular number: `(n^2 + n) / 2`

**Examples:**
```
tri(1) = 1
tri(4) = 10
tri(36) = 666
tri(100) = 5050
```

#### `qtri(x)`
Inverse triangular function. Returns n if x = tri(n), otherwise returns None (causes no match in search).

**Examples:**
```
qtri(666) = 36      # because tri(36) = 666
qtri(10) = 4        # because tri(4) = 10
qtri(5) = None      # 5 is not a triangular number
```

#### `is_triangular(x)`
Returns 1 if x is a triangular number, 0 otherwise.

**Examples:**
```
is_triangular(666) = 1
is_triangular(667) = 0
```

#### `trisum(b)`
Row-sum of the digit triangle for base b. This is stf(b) from the original paper.

**Examples:**
```
trisum(10) = 666    # 0123 + 456 + 78 + 9 in base 10
```

### Sequence Functions

#### `fibonacci(n)`
The nth Fibonacci number (1-indexed).

**Examples:**
```
fibonacci(1) = 1
fibonacci(2) = 1
fibonacci(10) = 55
fibonacci(20) = 6765
```

#### `factorial(n)`
n factorial: `n! = 1 * 2 * ... * n`

**Examples:**
```
factorial(5) = 120
factorial(10) = 3628800
```

#### `catalan(n)`
The nth Catalan number.

**Examples:**
```
catalan(0) = 1
catalan(5) = 42
catalan(10) = 16796
```

### Utility Functions

#### `digital_root(x)`
The digital root (repeated digit sum until single digit).

**Examples:**
```
digital_root(666) = 9     # 6+6+6 = 18, 1+8 = 9
digital_root(12345) = 6   # 1+2+3+4+5 = 15, 1+5 = 6
```

### Math Functions (v0.7.8+)

Built-in wrappers around Python's math operations.

#### `pow(base, exp)`
Raise base to the power of exp.

**Examples:**
```
pow(5, 2) = 25        # 5 squared
pow(2, 10) = 1024     # 2^10
pow(0.5, 2) = 0.25    # works with floats
```

#### `abs(x)`
Return the absolute value of x.

**Examples:**
```
abs(-5) = 5
abs(3) = 3
```

#### `mod(a, b)`
Return a modulo b (remainder of a / b).

**Examples:**
```
mod(10, 3) = 1
mod(7, 2) = 1
mod(6, 3) = 0
```

#### `sqrt(x)`
Return the square root of x. Returns int for perfect squares, float otherwise.

**Examples:**
```
sqrt(25) = 5          # perfect square → int
sqrt(2) = 1.41421...  # not perfect → float
sqrt(144) = 12
```

#### `floor(x)`
Round x down to the nearest integer.

**Examples:**
```
floor(3.7) = 3
floor(-1.5) = -2
```

#### `ceil(x)`
Round x up to the nearest integer.

**Examples:**
```
ceil(3.2) = 4
ceil(-1.5) = -1
```

## Custom Functions

You can define custom functions in a Python file and load them with `--functions`:

### Creating Custom Functions

Create a file `my_funcs.py`:

```python
def sum_of_digits(n):
    """Sum of digits of n."""
    return sum(int(d) for d in str(abs(n)))

def is_palindrome(n):
    """Return 1 if n is a palindrome, 0 otherwise."""
    s = str(n)
    return 1 if s == s[::-1] else 0
```

### Using Custom Functions

```bash
python prime-square-sum.py --functions my_funcs.py --expr "does_exist square(n) == 666"
python prime-square-sum.py --functions my_funcs.py --expr "does_exist is_palindrome(primesum(n,2)) == 1"
```

### Function Requirements

Custom functions must:
- Accept integer arguments
- Return an integer (or None to indicate no valid result)
- Be deterministic (same input = same output)
- Have no side effects

### Loading Multiple Function Files

```bash
python prime-square-sum.py --functions funcs1.py --functions funcs2.py --expr "..."
```

## Function Composition

Functions can be nested:

```bash
# Is there an n where tri(qtri(primesum(n,2))) equals something?
--expr "does_exist tri(qtri(primesum(n,2))) == 666"

# Find n where digital_root of primesum equals 9
--expr "does_exist digital_root(primesum(n,2)) == 9"
```

## Type Handling

All sequence functions use consistent type coercion (v0.7.7+):

### Accepted Types

| Input | Result | Example |
|-------|--------|---------|
| Integer | Passed through | `primesum(7, 2)` |
| Integral float | Converted to int | `primesum(7.0, 2)` → `primesum(7, 2)` |
| numpy integer | Converted to int | Works with numpy arrays |
| Non-integral float | **Error** | `primesum(7.5, 2)` raises `ValueError` |

### Error Messages

```python
# Non-integral float
>>> primesum(7.5, 2)
ValueError: primesum() requires integral value, got 7.5

# Wrong type
>>> primesum("7", 2)
TypeError: primesum() requires int, got str
```

### Bounded Types for External Libraries

When using iterators with dtype constraints, values are validated:

| dtype | Range | Library |
|-------|-------|---------|
| `uint64` | 0 to 2⁶⁴-1 | primesieve |
| `int32` | -2³¹ to 2³¹-1 | cupy |
| `int64` | -2⁶³ to 2⁶³-1 | cupy |

## See Also

- [expressions.md](expressions.md) - Expression syntax
- [equations.md](equations.md) - Saved equations
