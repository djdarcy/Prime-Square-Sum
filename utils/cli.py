"""
CLI utilities for expression building and configuration.
=========================================================

Provides:
- ExpressionComponents dataclass for decomposed expressions
- Expression building from CLI flags
- Equation loading (stub for Issue #21)
- Configuration loading (stub for Issue #22)

Issue: #18 (CLI rewrite)
Epic: #13 (Generalized Expression Grammar)
"""

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional
import json


# =============================================================================
# Expression Components
# =============================================================================

@dataclass
class ExpressionComponents:
    """
    Components of a decomposed expression.

    An expression has the form:
        <quantifier> <lhs> <operator> <rhs>

    Example:
        does_exist primesum(n,2) == 666
    """
    quantifier: str = "does_exist"
    lhs: str = "primesum(n,2)"
    operator: str = "=="
    rhs: Optional[str] = None

    def to_expression(self) -> str:
        """Build expression string from components."""
        if self.rhs is None:
            raise ValueError("RHS (--rhs or --target) is required")
        return f"{self.quantifier} {self.lhs} {self.operator} {self.rhs}"


# Built-in defaults
DEFAULTS = ExpressionComponents()

# Default bounds for variables
DEFAULT_BOUNDS = {
    'n': 1000000,
    'm': 10000,
}


# =============================================================================
# Expression Building
# =============================================================================

def build_expression_from_args(args) -> str:
    """
    Build expression string from CLI arguments.

    Priority:
    1. --expr (full expression, use as-is)
    2. --equation (load from file, apply overrides) [stub for #21]
    3. Decomposed flags (--lhs, --rhs, --operator, --quantifier)

    Args:
        args: Parsed argparse namespace

    Returns:
        Expression string ready for parsing

    Raises:
        ValueError: If required arguments are missing
    """
    # Tier 1: Full expression takes precedence
    if args.expr:
        return args.expr

    # Tier 3: Saved equation (stub for Issue #21)
    if args.equation:
        return _load_equation_expression(args)

    # Tier 2: Decomposed flags
    components = ExpressionComponents(
        quantifier=args.quantifier or DEFAULTS.quantifier,
        lhs=args.lhs or DEFAULTS.lhs,
        operator=args.operator or DEFAULTS.operator,
        rhs=args.rhs,
    )

    return components.to_expression()


def build_bounds_from_args(args, expr_str: str) -> Dict[str, int]:
    """
    Build bounds dictionary from CLI arguments.

    Args:
        args: Parsed argparse namespace
        expr_str: Expression string (used to detect variables)

    Returns:
        Dictionary mapping variable names to max values
    """
    bounds = {}

    # Add explicit bounds from args
    if hasattr(args, 'max_n') and args.max_n is not None:
        bounds['n'] = args.max_n
    if hasattr(args, 'max_m') and args.max_m is not None:
        bounds['m'] = args.max_m

    # Apply defaults for missing bounds
    for var, default in DEFAULT_BOUNDS.items():
        if var not in bounds:
            bounds[var] = default

    return bounds


# =============================================================================
# Equation Loading (Stub for Issue #21)
# =============================================================================

@dataclass
class SavedEquation:
    """
    A saved equation definition.

    Loaded from equations.json file.
    """
    id: str
    name: str
    lhs: str
    operator: str = "=="
    quantifier: str = "does_exist"
    rhs: Optional[str] = None
    defaults: Dict[str, int] = field(default_factory=dict)
    description: str = ""


def _load_equation_expression(args) -> str:
    """
    Load equation and build expression with overrides.

    Stub implementation for Issue #21.
    Currently raises NotImplementedError.
    """
    # TODO: Issue #21 - Implement equation loading
    # 1. Find equations.json file
    # 2. Load equation by ID or name
    # 3. Apply CLI overrides
    # 4. Return expression string

    raise NotImplementedError(
        f"Saved equations not yet implemented (Issue #21). "
        f"Use --expr or decomposed flags instead.\n"
        f"Example: --lhs \"primesum(n,2)\" --rhs 666"
    )


def list_equations() -> List[SavedEquation]:
    """
    List available saved equations.

    Stub implementation for Issue #21.
    """
    # TODO: Issue #21 - Implement equation listing
    print("Saved equations not yet implemented (Issue #21).")
    print("This feature will be available in v0.7.3.")
    return []


def find_equations_file() -> Optional[Path]:
    """
    Find equations.json in search path.

    Search order:
    1. ./equations.json (current directory)
    2. ~/.config/prime-square-sum/equations.json

    Stub implementation for Issue #21.
    """
    search_paths = [
        Path.cwd() / 'equations.json',
        Path.home() / '.config' / 'prime-square-sum' / 'equations.json',
    ]
    for path in search_paths:
        if path.exists():
            return path
    return None


# =============================================================================
# Configuration Loading (Stub for Issue #22)
# =============================================================================

@dataclass
class Config:
    """
    User configuration.

    Loaded from config.json file.
    """
    default_equation: Optional[str] = None
    default_bounds: Dict[str, int] = field(default_factory=dict)
    output_format: str = "text"


def load_config() -> Config:
    """
    Load configuration from config.json.

    Stub implementation for Issue #22.
    Currently returns default config.
    """
    # TODO: Issue #22 - Implement config loading
    # 1. Find config.json file
    # 2. Parse and validate
    # 3. Return Config object

    return Config()


def find_config_file() -> Optional[Path]:
    """
    Find config.json in search path.

    Search order:
    1. ./config.json (current directory)
    2. ~/.config/prime-square-sum/config.json

    Stub implementation for Issue #22.
    """
    search_paths = [
        Path.cwd() / 'config.json',
        Path.home() / '.config' / 'prime-square-sum' / 'config.json',
    ]
    for path in search_paths:
        if path.exists():
            return path
    return None


# =============================================================================
# Output Formatting
# =============================================================================

def format_match(match: Dict[str, int], format_type: str = "text") -> str:
    """
    Format a match result for output.

    Args:
        match: Dictionary mapping variable names to values
        format_type: One of "text", "json", "csv"

    Returns:
        Formatted string
    """
    if format_type == "json":
        return json.dumps({"found": True, "variables": match})
    elif format_type == "csv":
        if not match:
            return "found"
        keys = sorted(match.keys())
        return ",".join(f"{k}={match[k]}" for k in keys)
    else:  # text
        if not match:
            return "Found: (no variables)"
        return "Found: " + ", ".join(f"{k}={v}" for k, v in sorted(match.items()))


def format_no_match(format_type: str = "text") -> str:
    """
    Format a no-match result for output.

    Args:
        format_type: One of "text", "json", "csv"

    Returns:
        Formatted string
    """
    if format_type == "json":
        return json.dumps({"found": False, "variables": None})
    elif format_type == "csv":
        return "not_found"
    else:  # text
        return "No match found within bounds."
