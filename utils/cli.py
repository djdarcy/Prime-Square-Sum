"""
CLI utilities for expression building and configuration.
=========================================================

Provides:
- ExpressionComponents dataclass for decomposed expressions
- Expression building from CLI flags
- Equation loading from equations.json (Issue #21)
- Configuration loading from config.json (Issue #22)
- Parameter variable substitution (--var flag)

Issues: #18 (CLI rewrite), #21 (Saved Equations), #22 (Configuration)
Epic: #13 (Generalized Expression Grammar)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union, TYPE_CHECKING
import json
import re
import warnings


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

def build_expression_from_args(
    args,
    equations_file: Optional[EquationsFile] = None,
    config: Optional[Config] = None
) -> str:
    """
    Build expression string from CLI arguments.

    Priority:
    1. --expr (full expression, use as-is)
    2. --equation (load specific equation from file, apply overrides)
    3. Decomposed flags with default equation fallback

    The three-tier default system applies when using decomposed flags:
    - config.json default_equation > equations.json default:true > hardcoded

    Args:
        args: Parsed argparse namespace
        equations_file: Pre-loaded EquationsFile, or None to load
        config: Pre-loaded Config, or None to load

    Returns:
        Expression string ready for parsing

    Raises:
        ValueError: If required arguments are missing
    """
    # Tier 1: Full expression takes precedence
    if args.expr:
        return args.expr

    # Tier 2: Explicit --equation flag
    if args.equation:
        return _load_equation_expression(args, equations_file)

    # Tier 3: Decomposed flags with default equation fallback
    # Load equations and config if not provided
    if equations_file is None:
        try:
            equations_file = load_equations_file()
        except ValueError:
            equations_file = None

    if config is None:
        config = load_config()

    # Check if user provided any decomposed flags
    has_decomposed = any([
        args.lhs,
        args.operator,
        args.quantifier,
    ])

    # If user only provided --rhs (or --target), use default equation
    if not has_decomposed and args.rhs:
        default_eq, source = resolve_default_equation(equations_file, config)

        if default_eq:
            # Parse --var arguments
            var_overrides = {}
            if hasattr(args, 'var') and args.var:
                for var_str in args.var:
                    var_overrides.update(parse_var_string(var_str))

            components = default_eq.to_components(var_overrides)
            components.rhs = args.rhs
            return components.to_expression()

    # Fall back to hardcoded defaults with any CLI overrides
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
# Equation Loading (Issue #21)
# =============================================================================

@dataclass
class ParameterDef:
    """Definition of a substitutable parameter in an equation."""
    default: Any
    type: str = "auto"  # "int", "float", "str", or "auto"
    description: str = ""


@dataclass
class IteratorDef:
    """Definition of an iterator variable (placeholder for Issue #24)."""
    start: Union[int, float] = 1
    max: Optional[Union[int, float]] = None
    step_func: Optional[str] = None  # Future: "linear_step(1)", etc.
    type: str = "int"  # "int" or "float"


@dataclass
class SavedEquation:
    """
    A saved equation definition.

    Loaded from equations.json file.

    Supports two formats:
    1. Decomposed: lhs, operator, quantifier, rhs fields
    2. Full expression: expression field (e.g., for verify mode)
    """
    id: str
    name: str
    lhs: Optional[str] = None  # For decomposed format
    operator: str = "=="
    quantifier: str = "does_exist"
    rhs: Optional[str] = None
    expression: Optional[str] = None  # For full expression format (Issue #34)
    is_default: bool = False
    parameters: Dict[str, ParameterDef] = field(default_factory=dict)
    iterators: Dict[str, IteratorDef] = field(default_factory=dict)
    defaults: Dict[str, int] = field(default_factory=dict)
    description: str = ""

    def to_expression_string(self, var_overrides: Optional[Dict[str, Any]] = None) -> str:
        """
        Convert to full expression string.

        If 'expression' field is set, returns it directly.
        Otherwise, builds from components (lhs, operator, rhs, quantifier).

        Args:
            var_overrides: Dict of parameter overrides from --var flag

        Returns:
            Full expression string ready for parsing
        """
        # If we have a direct expression, use it (e.g., verify equations)
        if self.expression:
            return self.expression

        # Otherwise build from components
        components = self.to_components(var_overrides)
        return components.to_expression()

    def to_components(self, var_overrides: Optional[Dict[str, Any]] = None) -> 'ExpressionComponents':
        """
        Convert to ExpressionComponents with parameter substitution.

        Note: For equations with 'expression' field, use to_expression_string() instead.

        Args:
            var_overrides: Dict of parameter overrides from --var flag

        Returns:
            ExpressionComponents with parameters substituted

        Raises:
            ValueError: If equation uses 'expression' format instead of components
        """
        if self.expression and not self.lhs:
            raise ValueError(
                f"Equation '{self.name}' uses 'expression' format. "
                "Use to_expression_string() instead."
            )

        # Start with equation's LHS and RHS
        lhs = self.lhs
        rhs = self.rhs

        # Build parameter values: defaults + overrides
        param_values = {}
        for name, param_def in self.parameters.items():
            param_values[name] = param_def.default

        if var_overrides:
            for name, value in var_overrides.items():
                if name in self.parameters:
                    # Cast to expected type
                    param_values[name] = _cast_parameter(
                        value,
                        self.parameters[name].type
                    )
                else:
                    warnings.warn(
                        f"Unknown parameter '{name}' for equation '{self.name}'. "
                        f"Available: {list(self.parameters.keys())}"
                    )

        # Substitute parameters in LHS and RHS
        for name, value in param_values.items():
            lhs = lhs.replace(name, str(value))
            if rhs:
                rhs = rhs.replace(name, str(value))

        return ExpressionComponents(
            quantifier=self.quantifier,
            lhs=lhs,
            operator=self.operator,
            rhs=rhs,
        )


@dataclass
class EquationsFile:
    """
    Parsed equations.json file.

    Contains all equations and tracks which one is marked as default.
    """
    version: str
    equations: Dict[str, SavedEquation]
    default_id: Optional[str] = None
    source_path: Optional[Path] = None

    def get_equation(self, id_or_name: str) -> Optional[SavedEquation]:
        """
        Look up equation by ID or name.

        Args:
            id_or_name: Equation ID (e.g., "1") or name (e.g., "primesum-squared")

        Returns:
            SavedEquation if found, None otherwise
        """
        # Try by ID first
        if id_or_name in self.equations:
            return self.equations[id_or_name]

        # Try by name
        for eq in self.equations.values():
            if eq.name == id_or_name:
                return eq

        return None

    def get_default(self) -> Optional[SavedEquation]:
        """Get the default equation, if one is marked."""
        if self.default_id:
            return self.equations.get(self.default_id)
        return None


def _cast_parameter(value: str, type_hint: str) -> Any:
    """
    Cast a parameter value to the expected type.

    Args:
        value: String value from CLI
        type_hint: Expected type ("int", "float", "str", "auto")

    Returns:
        Casted value
    """
    if type_hint == "int":
        return int(float(value))  # Handle "3.0" -> 3
    elif type_hint == "float":
        return float(value)
    elif type_hint == "str":
        return str(value)
    else:  # auto
        # Try int first, then float, then str
        try:
            if '.' in value or 'e' in value.lower():
                return float(value)
            return int(value)
        except ValueError:
            return value


def parse_var_string(var_string: str) -> Dict[str, str]:
    """
    Parse --var argument string into dict.

    Supports:
    - "a=3" -> {"a": "3"}
    - "a=3,b=4" -> {"a": "3", "b": "4"}
    - "a:int=3.14" -> {"a": "3.14"} (type hint parsed separately)

    Args:
        var_string: Variable assignment string

    Returns:
        Dict mapping variable names to string values
    """
    result = {}
    # Split on comma, but handle potential spaces
    parts = [p.strip() for p in var_string.split(',')]

    for part in parts:
        if '=' not in part:
            warnings.warn(f"Invalid --var format: '{part}'. Expected 'name=value'")
            continue

        # Handle type hints like "a:int=3"
        name_part, value = part.split('=', 1)

        # Strip type hint if present (we'll use equation's type hint)
        if ':' in name_part:
            name = name_part.split(':')[0]
        else:
            name = name_part

        result[name.strip()] = value.strip()

    return result


def find_equations_file() -> Optional[Path]:
    """
    Find equations.json in search path.

    Search order:
    1. ./equations.json (current directory)
    2. ~/.config/prime-square-sum/equations.json
    3. Package directory equations.json (shipped default)

    Returns:
        Path to equations.json if found, None otherwise
    """
    search_paths = [
        Path.cwd() / 'equations.json',
        Path.home() / '.config' / 'prime-square-sum' / 'equations.json',
        Path(__file__).parent.parent / 'equations.json',  # Package dir
    ]
    for path in search_paths:
        if path.exists():
            return path
    return None


def load_equations_file(path: Optional[Path] = None) -> Optional[EquationsFile]:
    """
    Load and parse equations.json file.

    Args:
        path: Path to equations.json, or None to search

    Returns:
        EquationsFile if found and valid, None otherwise

    Raises:
        ValueError: If file exists but is malformed
    """
    if path is None:
        path = find_equations_file()

    if path is None:
        return None

    try:
        with open(path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        raise ValueError(f"Invalid JSON in {path}: {e}")
    except IOError as e:
        raise ValueError(f"Cannot read {path}: {e}")

    # Validate version
    version = data.get('version', '1.0')
    if not version.startswith('1.'):
        warnings.warn(
            f"equations.json version {version} may not be fully compatible. "
            f"Expected version 1.x"
        )

    # Parse equations
    equations = {}
    default_id = None

    for eq_id, eq_data in data.get('equations', {}).items():
        # Parse parameters
        parameters = {}
        for param_name, param_data in eq_data.get('parameters', {}).items():
            if isinstance(param_data, dict):
                parameters[param_name] = ParameterDef(
                    default=param_data.get('default'),
                    type=param_data.get('type', 'auto'),
                    description=param_data.get('description', ''),
                )
            else:
                # Simple format: "a": 2 instead of "a": {"default": 2}
                parameters[param_name] = ParameterDef(default=param_data)

        # Parse iterators (placeholder for Issue #24)
        iterators = {}
        for iter_name, iter_data in eq_data.get('iterators', {}).items():
            if isinstance(iter_data, dict):
                iterators[iter_name] = IteratorDef(
                    start=iter_data.get('start', 1),
                    max=iter_data.get('max'),
                    step_func=iter_data.get('step_func'),
                    type=iter_data.get('type', 'int'),
                )

        # Validate required fields - either 'lhs' or 'expression' is required
        if 'lhs' not in eq_data and 'expression' not in eq_data:
            warnings.warn(
                f"Equation '{eq_id}' missing required 'lhs' or 'expression' field, skipping"
            )
            continue

        eq = SavedEquation(
            id=eq_id,
            name=eq_data.get('name', eq_id),
            lhs=eq_data.get('lhs'),  # May be None for expression-based equations
            operator=eq_data.get('operator', '=='),
            quantifier=eq_data.get('quantifier', 'does_exist'),
            rhs=eq_data.get('rhs'),
            expression=eq_data.get('expression'),  # New: full expression format
            is_default=eq_data.get('default', False),
            parameters=parameters,
            iterators=iterators,
            defaults=eq_data.get('defaults', {}),
            description=eq_data.get('description', ''),
        )
        equations[eq_id] = eq

        # Track default
        if eq.is_default:
            if default_id is None:
                default_id = eq_id
            else:
                warnings.warn(
                    f"Multiple default equations found: '{default_id}' and '{eq_id}'. "
                    f"Using '{default_id}'."
                )

    return EquationsFile(
        version=version,
        equations=equations,
        default_id=default_id,
        source_path=path,
    )


def list_equations(equations_file: Optional[EquationsFile] = None) -> List[SavedEquation]:
    """
    List available saved equations.

    Args:
        equations_file: Pre-loaded EquationsFile, or None to load

    Returns:
        List of SavedEquation objects
    """
    if equations_file is None:
        equations_file = load_equations_file()

    if equations_file is None:
        return []

    return list(equations_file.equations.values())


def print_equations_list(equations_file: Optional[EquationsFile] = None) -> None:
    """
    Print formatted list of available equations.

    Args:
        equations_file: Pre-loaded EquationsFile, or None to load
    """
    if equations_file is None:
        equations_file = load_equations_file()

    if equations_file is None:
        print("No equations.json found.")
        print("Search paths:")
        print("  - ./equations.json")
        print("  - ~/.config/prime-square-sum/equations.json")
        return

    print(f"\nAvailable Equations (from {equations_file.source_path}):")
    print("=" * 70)

    for eq_id in sorted(equations_file.equations.keys(), key=lambda x: (not x.isdigit(), x)):
        eq = equations_file.equations[eq_id]
        default_marker = " [DEFAULT]" if eq.is_default else ""
        print(f"\n  {eq_id}: {eq.name}{default_marker}")
        # Show full expression or decomposed format
        if eq.expression:
            print(f"      {eq.expression}")
        else:
            print(f"      {eq.quantifier} {eq.lhs} {eq.operator} {eq.rhs or '<rhs>'}")
        if eq.description:
            print(f"      {eq.description}")
        if eq.parameters:
            params = ", ".join(f"{k}={v.default}" for k, v in eq.parameters.items())
            print(f"      Parameters: {params}")

    print("\n" + "=" * 70)
    print(f"Total: {len(equations_file.equations)} equations")


def _load_equation_expression(args, equations_file: Optional[EquationsFile] = None) -> str:
    """
    Load equation and build expression with overrides.

    Args:
        args: Parsed argparse namespace with equation, var, lhs, rhs, etc.
        equations_file: Pre-loaded EquationsFile, or None to load

    Returns:
        Expression string ready for parsing

    Raises:
        ValueError: If equation not found or required args missing
    """
    if equations_file is None:
        equations_file = load_equations_file()

    if equations_file is None:
        raise ValueError(
            f"No equations.json found. Cannot load equation '{args.equation}'.\n"
            f"Create equations.json or use --expr instead."
        )

    # Look up equation
    eq = equations_file.get_equation(args.equation)
    if eq is None:
        available = ", ".join(
            f"{e.id} ({e.name})" for e in equations_file.equations.values()
        )
        raise ValueError(
            f"Equation '{args.equation}' not found.\n"
            f"Available equations: {available}"
        )

    # Parse --var arguments
    var_overrides = {}
    if hasattr(args, 'var') and args.var:
        for var_str in args.var:
            var_overrides.update(parse_var_string(var_str))

    # If equation uses 'expression' format (e.g., verify equations), return directly
    if eq.expression and not eq.lhs:
        # Expression-based equations don't support CLI overrides
        if any([args.lhs, args.rhs, args.operator, args.quantifier]):
            warnings.warn(
                f"Equation '{eq.name}' uses 'expression' format. "
                "CLI overrides (--lhs, --rhs, etc.) are ignored."
            )
        return eq.to_expression_string(var_overrides)

    # Convert to components with parameter substitution
    components = eq.to_components(var_overrides)

    # Apply CLI overrides (CLI takes precedence)
    if args.lhs:
        components.lhs = args.lhs
    if args.rhs:
        components.rhs = args.rhs
    if args.operator:
        components.operator = args.operator
    if args.quantifier:
        components.quantifier = args.quantifier

    return components.to_expression()


# =============================================================================
# Configuration Loading (Issue #22)
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
    source_path: Optional[Path] = None
    # Algorithm settings (Issue #29)
    algorithms: Dict[str, str] = field(default_factory=dict)
    max_memory_mb: Optional[int] = None
    prefer: Optional[str] = None


def find_config_file() -> Optional[Path]:
    """
    Find config.json in search path.

    Search order:
    1. ./config.json (current directory)
    2. ~/.config/prime-square-sum/config.json

    Returns:
        Path to config.json if found, None otherwise
    """
    search_paths = [
        Path.cwd() / 'config.json',
        Path.home() / '.config' / 'prime-square-sum' / 'config.json',
    ]
    for path in search_paths:
        if path.exists():
            return path
    return None


def load_config(path: Optional[Path] = None) -> Config:
    """
    Load configuration from config.json.

    Args:
        path: Path to config.json, or None to search

    Returns:
        Config object (defaults if no file found)
    """
    if path is None:
        path = find_config_file()

    if path is None:
        return Config()

    try:
        with open(path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except (json.JSONDecodeError, IOError) as e:
        warnings.warn(f"Cannot load config from {path}: {e}")
        return Config()

    return Config(
        default_equation=data.get('default_equation'),
        default_bounds=data.get('default_bounds', {}),
        output_format=data.get('output_format', 'text'),
        source_path=path,
        # Algorithm settings (Issue #29)
        algorithms=data.get('algorithms', {}),
        max_memory_mb=data.get('max_memory_mb'),
        prefer=data.get('prefer'),
    )


def resolve_default_equation(
    equations_file: Optional[EquationsFile],
    config: Config
) -> Tuple[Optional[SavedEquation], str]:
    """
    Resolve which equation is the default using three-tier precedence.

    Precedence:
    1. config.json "default_equation" (highest)
    2. equations.json "default": true
    3. Hardcoded built-in (lowest)

    Args:
        equations_file: Loaded equations file (may be None)
        config: Loaded config

    Returns:
        (equation, source) where source describes where default came from:
        - "config": from config.json default_equation
        - "equations": from equations.json default: true marker
        - "hardcoded": built-in default
    """
    # Tier 1: config.json default_equation
    if config.default_equation and equations_file:
        eq = equations_file.get_equation(config.default_equation)
        if eq:
            return (eq, "config")
        else:
            warnings.warn(
                f"config.json default_equation '{config.default_equation}' "
                f"not found in equations.json"
            )

    # Tier 2: equations.json default: true
    if equations_file:
        eq = equations_file.get_default()
        if eq:
            return (eq, "equations")

    # Tier 3: hardcoded
    return (None, "hardcoded")


def show_config(
    equations_file: Optional[EquationsFile] = None,
    config: Optional[Config] = None
) -> None:
    """
    Display effective configuration.

    Shows which default is active and the assembled expression format.
    """
    if equations_file is None:
        equations_file = load_equations_file()
    if config is None:
        config = load_config()

    default_eq, source = resolve_default_equation(equations_file, config)

    print("\nConfiguration")
    print("=" * 50)

    # Source files
    print("\nSource files:")
    if equations_file and equations_file.source_path:
        print(f"  equations: {equations_file.source_path}")
    else:
        print("  equations: (none)")
    if config.source_path:
        print(f"  config:    {config.source_path}")
    else:
        print("  config:    (none)")

    # Default equation
    print(f"\nDefault equation: ", end="")
    if default_eq:
        print(f"{default_eq.name} (from {source})")
    else:
        print(f"(hardcoded built-in)")

    # Effective expression
    print("\nEffective expression:")
    if default_eq:
        components = default_eq.to_components()
        rhs_display = components.rhs or "<rhs>"
        print(f'  --expr "{components.quantifier} {components.lhs} {components.operator} {rhs_display}"')
        if default_eq.parameters:
            params = ", ".join(f"{k}={v.default}" for k, v in default_eq.parameters.items())
            print(f"  Parameters: {params}")
    else:
        print(f'  --expr "does_exist primesum(n,2) == <rhs>"')

    # Default bounds
    print("\nDefault bounds:")
    bounds = {**DEFAULT_BOUNDS, **config.default_bounds}
    if default_eq:
        bounds.update(default_eq.defaults)
    for var, val in sorted(bounds.items()):
        print(f"  --max-{var} {val}")

    # Output format
    print(f"\nOutput format: {config.output_format}")

    # Algorithm settings (Issue #29)
    print("\nAlgorithm settings:")
    if config.algorithms:
        for algo_class, variant in config.algorithms.items():
            print(f"  {algo_class}: {variant}")
    else:
        print("  (auto-detection)")
    if config.max_memory_mb:
        print(f"  max_memory: {config.max_memory_mb} MB")
    if config.prefer:
        print(f"  prefer: {config.prefer}")
    print()


# =============================================================================
# Output Formatting
# =============================================================================

def format_match(match: Dict[str, Any], format_type: str = "text") -> str:
    """
    Format a match result for output.

    Args:
        match: Dictionary mapping variable names to values, or
               {"__verify_result__": bool} for verify mode
        format_type: One of "text", "json", "csv"

    Returns:
        Formatted string
    """
    # Handle verify mode result
    if "__verify_result__" in match:
        result = match["__verify_result__"]
        if format_type == "json":
            return json.dumps({"verified": result})
        elif format_type == "csv":
            return "true" if result else "false"
        else:  # text
            return "true" if result else "false"

    # Standard match result
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
