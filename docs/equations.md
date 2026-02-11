# Saved Equations

Save frequently-used expressions in `equations.json` for quick access.

## Quick Start

```bash
# List available equations
python prime-square-sum.py --list equations

# Run an equation by name
python prime-square-sum.py --equation primesum-squared

# Run by ID
python prime-square-sum.py --equation 1

# Verify stf(10) = 666
python prime-square-sum.py --equation verify-stf10
```

## equations.json Format

The `equations.json` file contains saved equations indexed by ID:

```json
{
  "1": {
    "name": "primesum-squared",
    "lhs": "primesum(n,2)",
    "description": "Sum of squared primes",
    "default": true
  },
  "2": {
    "name": "primesum-cubed",
    "lhs": "primesum(n,3)",
    "description": "Sum of cubed primes"
  },
  "5": {
    "name": "verify-stf10",
    "expression": "verify primesum(7,2) == 666",
    "description": "Verify stf(10) = 666 from 2010 paper"
  }
}
```

## Equation Fields

### Required Fields

| Field | Description |
|-------|-------------|
| `name` | Unique identifier for `--equation name` |

### Expression Format (choose one)

**Decomposed format** - for search queries:
```json
{
  "lhs": "primesum(n,2)",
  "rhs": "666",
  "operator": "==",
  "quantifier": "does_exist"
}
```

**Full expression format** - for any expression including verify:
```json
{
  "expression": "verify primesum(7,2) == 666"
}
```

### Optional Fields

| Field | Description | Default |
|-------|-------------|---------|
| `description` | Human-readable description | - |
| `default` | Mark as default equation | `false` |
| `operator` | Comparison operator | `==` |
| `quantifier` | `does_exist`, `for_any`, `verify`, `solve` | `does_exist` |
| `bounds` | Variable bounds | - |
| `parameters` | User-configurable parameters | - |

## Default Equation

Mark one equation with `"default": true` to use it when no target or expression is specified:

```json
{
  "1": {
    "name": "primesum-squared",
    "lhs": "primesum(n,2)",
    "default": true
  }
}
```

Override in `config.json`:
```json
{
  "default_equation": "primesum-cubed"
}
```

## Parameters

Equations can define parameters that users can override with `--var`:

```json
{
  "10": {
    "name": "primesum-power",
    "lhs": "primesum(n,p)",
    "description": "Sum of primes to power p",
    "parameters": {
      "p": {
        "default": 2,
        "description": "Power to raise primes to"
      }
    }
  }
}
```

Usage:
```bash
# Use default power (2)
python prime-square-sum.py --equation primesum-power --target 666

# Override power
python prime-square-sum.py --equation primesum-power --target 666 --var p=3
```

## Custom Bounds

Set default variable bounds in the equation:

```json
{
  "20": {
    "name": "tri-match",
    "lhs": "primesum(n,2)",
    "rhs": "tri(m)",
    "quantifier": "for_any",
    "bounds": {
      "n": 1000,
      "m": 5000
    }
  }
}
```

CLI flags override equation bounds:
```bash
python prime-square-sum.py --equation tri-match --max n:500
```

## Built-in Equations

| ID | Name | Description |
|----|------|-------------|
| 1 | `primesum-squared` | Sum of squared primes (default) |
| 2 | `primesum-cubed` | Sum of cubed primes |
| 3 | `tri-match` | Prime sums vs triangular numbers |
| 4 | `fib-match` | Prime sums vs Fibonacci numbers |
| 5 | `verify-stf10` | Verify stf(10) = 666 |

## Creating Custom Equations

1. Open `equations.json` in your project root
2. Add a new entry with a unique ID:

```json
{
  "100": {
    "name": "my-custom-equation",
    "expression": "for_any primesum(n,2) == fibonacci(m)",
    "description": "Find prime sums that are also Fibonacci numbers",
    "bounds": {
      "n": 100,
      "m": 50
    }
  }
}
```

3. Run it:
```bash
python prime-square-sum.py --equation my-custom-equation
```

## Precedence

When multiple sources define defaults:

1. **CLI flags** (highest priority)
2. **config.json** settings
3. **equations.json** `default: true`
4. **Built-in defaults** (lowest priority)

## See Also

- [expressions.md](expressions.md) - Expression syntax reference
- [functions.md](functions.md) - Available functions
