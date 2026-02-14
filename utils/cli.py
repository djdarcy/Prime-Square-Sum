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

    # Add bounds from --max / --iter-stop
    if hasattr(args, 'iter_stop') and args.iter_stop:
        for spec in args.iter_stop:
            if ':' in spec:
                var_name, value = spec.split(':', 1)
                bounds[var_name.strip()] = int(value.strip())

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
    """
    Definition of an iterator variable.

    Used to configure how a variable iterates during expression evaluation.
    Supports integer and float types with various iteration modes.

    Issue: #24 (Custom Iterator Functions), #37 (Basic Iterator Protocol)
    """
    type: str = "int"  # "int" or "float"
    dtype: str = "int"  # Validation type: "int", "int32", "int64", "uint64", "float32", "float64"
    start: Union[int, float] = 1
    stop: Optional[Union[int, float]] = None  # End value (inclusive)
    step: Optional[Union[int, float]] = None  # Step size
    num_steps: Optional[int] = None  # For linspace-style (float only)
    precision: int = 10  # Decimal precision for float
    # Legacy field for backwards compatibility
    max: Optional[Union[int, float]] = None  # Alias for stop (deprecated)
    step_func: Optional[str] = None  # Future: custom step functions

    def __post_init__(self):
        """Handle legacy 'max' field."""
        if self.max is not None and self.stop is None:
            self.stop = self.max

    def to_iterator(self) -> "SequenceIterator":
        """
        Create a SequenceIterator from this definition.

        Returns:
            IntIterator or FloatIterator based on type

        Raises:
            ValueError: If configuration is invalid
        """
        from utils.iterators import IntIterator, FloatIterator

        if self.type == "int":
            step = self.step if self.step is not None else 1
            stop = self.stop if self.stop is not None else 1000000
            return IntIterator(
                start=int(self.start),
                stop=int(stop),
                step=int(step),
                dtype=self.dtype if self.dtype in ("int", "int32", "int64", "uint64") else "int",
            )
        elif self.type == "float":
            stop = self.stop if self.stop is not None else 1.0
            return FloatIterator(
                start=float(self.start),
                stop=float(stop),
                step=float(self.step) if self.step is not None else None,
                num_steps=self.num_steps,
                precision=self.precision,
                dtype=self.dtype if self.dtype in ("float32", "float64") else "float64",
            )
        else:
            raise ValueError(f"Unknown iterator type: {self.type}")


# Forward reference for type hints
if TYPE_CHECKING:
    from utils.iterators import SequenceIterator


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
    # Imaginary literal syntax (Issue #54, Phase 2)
    imaginary_unit: str = 'none'


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
        imaginary_unit=data.get('imaginary_unit', 'none'),
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


def resolve_effective_bounds() -> Dict[str, int]:
    """
    Resolve the effective default bounds for display.

    Uses the same precedence as runtime:
    1. Equation-specific defaults (from default equation)
    2. config.json "default_bounds"
    3. Hardcoded DEFAULT_BOUNDS (lowest)

    Returns DEFAULT_BOUNDS on any error, so this is always safe to call.
    """
    try:
        bounds = dict(DEFAULT_BOUNDS)
        config = load_config()
        bounds.update(config.default_bounds)
        equations_file = load_equations_file()
        default_eq, _source = resolve_default_equation(equations_file, config)
        if default_eq and default_eq.defaults:
            bounds.update(default_eq.defaults)
        return bounds
    except Exception:
        pass
    return dict(DEFAULT_BOUNDS)


def resolve_effective_defaults() -> ExpressionComponents:
    """
    Resolve the effective default expression components for display.

    Uses the same three-tier precedence as runtime:
    1. config.json "default_equation" (highest)
    2. equations.json "default": true
    3. Hardcoded built-in (lowest)

    Returns hardcoded defaults on any error, so this is always safe to call.

    Returns:
        ExpressionComponents with the effective defaults (parameter-substituted).
    """
    try:
        equations_file = load_equations_file()
        config = load_config()
        default_eq, _source = resolve_default_equation(equations_file, config)
        if default_eq and default_eq.lhs:
            return default_eq.to_components()
    except Exception:
        pass
    return ExpressionComponents()


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
# Iterator Definition Parsing (Issue #37)
# =============================================================================

def parse_iterator_def(var_spec: str) -> Tuple[str, IteratorDef]:
    """
    Parse compact iterator definition syntax.

    Syntax: VAR:START:STOP[:STEP][:TYPE]

    Examples:
        "n:1:1000"           -> n from 1 to 1000, step 1, int
        "n:1:1000:2"         -> n from 1 to 1000, step 2, int
        "n:1:1000:1:uint64"  -> n from 1 to 1000, step 1, dtype uint64
        "x:0.0:1.0"          -> x from 0.0 to 1.0 (auto-detects float)
        "x:0.0:1.0:0.1"      -> x from 0.0 to 1.0, step 0.1
        "x:0.0:1.0::float32" -> x from 0.0 to 1.0, default step, dtype float32

    Args:
        var_spec: Compact iterator specification string

    Returns:
        Tuple of (variable_name, IteratorDef)

    Raises:
        ValueError: If syntax is invalid
    """
    parts = var_spec.split(':')

    if len(parts) < 3:
        raise ValueError(
            f"Invalid iterator syntax: '{var_spec}'. "
            f"Expected VAR:START:STOP[:STEP][:TYPE]"
        )

    var_name = parts[0].strip()
    if not var_name:
        raise ValueError(f"Empty variable name in: '{var_spec}'")

    try:
        start_str = parts[1].strip()
        stop_str = parts[2].strip()

        # Auto-detect type from values
        is_float = '.' in start_str or '.' in stop_str

        if is_float:
            start = float(start_str)
            stop = float(stop_str)
            iter_type = "float"
            default_dtype = "float64"
        else:
            start = int(start_str)
            stop = int(stop_str)
            iter_type = "int"
            default_dtype = "int"

    except ValueError as e:
        raise ValueError(f"Invalid start/stop values in: '{var_spec}' - {e}")

    # Parse optional step (parts[3])
    step = None
    if len(parts) > 3 and parts[3].strip():
        try:
            step_str = parts[3].strip()
            if is_float or '.' in step_str:
                step = float(step_str)
                iter_type = "float"  # Step with decimal forces float
            else:
                step = int(step_str)
        except ValueError as e:
            raise ValueError(f"Invalid step value in: '{var_spec}' - {e}")

    # Parse optional type/dtype (parts[4])
    dtype = default_dtype
    if len(parts) > 4 and parts[4].strip():
        dtype = parts[4].strip().lower()
        # Validate dtype
        valid_int_dtypes = {"int", "int32", "int64", "uint64"}
        valid_float_dtypes = {"float32", "float64"}
        if iter_type == "int" and dtype not in valid_int_dtypes:
            raise ValueError(
                f"Invalid dtype '{dtype}' for integer iterator. "
                f"Valid: {valid_int_dtypes}"
            )
        if iter_type == "float" and dtype not in valid_float_dtypes:
            raise ValueError(
                f"Invalid dtype '{dtype}' for float iterator. "
                f"Valid: {valid_float_dtypes}"
            )

    return var_name, IteratorDef(
        type=iter_type,
        dtype=dtype,
        start=start,
        stop=stop,
        step=step,
    )


def build_iterator_factories_from_args(
    args,
    bounds: Dict[str, int]
) -> Dict[str, "Callable[[], SequenceIterator]"]:
    """
    Build iterator factory functions from CLI arguments.

    This function bridges CLI arguments to the grammar's iterator_factories parameter.
    It handles:
    - --iter-var VAR:START:STOP[:STEP][:TYPE] compact syntax
    - --min/--max (aliases for --iter-start/--iter-stop)
    - --iter-type, --iter-step, etc. individual flags

    Args:
        args: Parsed argparse namespace
        bounds: Bounds dict from build_bounds_from_args()

    Returns:
        Dict mapping variable names to factory functions
    """
    from utils.iterators import IntIterator

    factories: Dict[str, Callable] = {}
    iterator_defs: Dict[str, IteratorDef] = {}

    # 1. Parse --var compact syntax (if present)
    if hasattr(args, 'iter_var') and args.iter_var:
        for var_spec in args.iter_var:
            try:
                var_name, iter_def = parse_iterator_def(var_spec)
                iterator_defs[var_name] = iter_def
            except ValueError as e:
                # Re-raise with context
                raise ValueError(f"Error parsing --var: {e}")

    # 2. Apply individual --iter-* overrides
    if hasattr(args, 'iter_type') and args.iter_type:
        for override in args.iter_type:
            var_name, value = _parse_iter_override(override, "type")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].type = value

    if hasattr(args, 'iter_start') and args.iter_start:
        for override in args.iter_start:
            var_name, value = _parse_iter_override(override, "start")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].start = _parse_numeric(value)

    if hasattr(args, 'iter_stop') and args.iter_stop:
        for override in args.iter_stop:
            var_name, value = _parse_iter_override(override, "stop")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].stop = _parse_numeric(value)

    if hasattr(args, 'iter_step') and args.iter_step:
        for override in args.iter_step:
            var_name, value = _parse_iter_override(override, "step")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].step = _parse_numeric(value)

    if hasattr(args, 'iter_num_steps') and args.iter_num_steps:
        for override in args.iter_num_steps:
            var_name, value = _parse_iter_override(override, "num_steps")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].num_steps = int(value)

    if hasattr(args, 'iter_dtype') and args.iter_dtype:
        for override in args.iter_dtype:
            var_name, value = _parse_iter_override(override, "dtype")
            if var_name not in iterator_defs:
                iterator_defs[var_name] = IteratorDef()
            iterator_defs[var_name].dtype = value.lower()

    # 3. Convert IteratorDefs to factory functions
    for var_name, iter_def in iterator_defs.items():
        # Capture iter_def in closure properly
        def make_factory(idef):
            return lambda: idef.to_iterator()
        factories[var_name] = make_factory(iter_def)

    # 4. For variables in bounds but not in factories, create default factories
    # (Default factories for variables with bounds but no explicit iterator)
    for var_name, max_val in bounds.items():
        if var_name not in factories:
            # Create a factory that uses the bound
            def make_bound_factory(stop):
                return lambda: IntIterator(1, stop, 1)
            factories[var_name] = make_bound_factory(max_val)

    return factories


def _parse_iter_override(override: str, field_name: str) -> Tuple[str, str]:
    """
    Parse VAR:VALUE format for --iter-* flags.

    Args:
        override: String in "VAR:VALUE" format
        field_name: Name of field being parsed (for error messages)

    Returns:
        Tuple of (variable_name, value_string)

    Raises:
        ValueError: If format is invalid
    """
    if ':' not in override:
        raise ValueError(
            f"Invalid --iter-{field_name} format: '{override}'. "
            f"Expected VAR:VALUE"
        )
    parts = override.split(':', 1)
    return parts[0].strip(), parts[1].strip()


def _parse_numeric(value: str) -> Union[int, float]:
    """Parse string to int or float based on content."""
    if '.' in value or 'e' in value.lower():
        return float(value)
    return int(value)


# Type hint for Callable
from typing import Callable


# =============================================================================
# Output Formatting
# =============================================================================

def _json_safe(value):
    """Convert a value to a JSON-serializable form (handles complex numbers)."""
    if isinstance(value, complex):
        return {"real": value.real, "imag": value.imag}
    return value


def format_match(match: Dict[str, Any], format_type: str = "text") -> str:
    """
    Format a match result for output.

    Args:
        match: Dictionary mapping variable names to values.
            Special keys:
            - "__verify_result__": bool — verify/truth-check mode
            - "__solve_result__": value — calculator mode
            - "__value__": value — value enumeration mode (alongside variable keys)
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

    # Handle solve/calculator mode result
    if "__solve_result__" in match:
        value = match["__solve_result__"]
        if format_type == "json":
            return json.dumps({"result": _json_safe(value)})
        else:  # text or csv
            return str(value)

    # Handle value enumeration mode
    if "__value__" in match:
        value = match["__value__"]
        var_items = sorted((k, v) for k, v in match.items() if not k.startswith("__"))
        if format_type == "json":
            return json.dumps({
                "variables": {k: v for k, v in var_items},
                "value": _json_safe(value)
            })
        elif format_type == "csv":
            return ",".join(str(v) for _, v in var_items) + "," + str(value)
        else:  # text
            vars_str = ", ".join(f"{k}={v}" for k, v in var_items)
            return f"{vars_str}: {value}"

    # Standard match result (comparison-based search)
    # Extract vals annotation if present
    vals = match.get("__vals__")
    ops = match.get("__ops__")
    var_items = sorted((k, v) for k, v in match.items() if not k.startswith("__"))

    if format_type == "json":
        result = {"found": True, "variables": {k: v for k, v in var_items}}
        if vals is not None:
            result["values"] = vals
        return json.dumps(result)
    elif format_type == "csv":
        if not var_items:
            return "found"
        line = ",".join(f"{k}={v}" for k, v in var_items)
        if vals is not None:
            line += "," + ",".join(str(v) for v in vals)
        return line
    else:  # text
        if not var_items:
            base = "Found: (no variables)"
        else:
            base = "Found: " + ", ".join(f"{k}={v}" for k, v in var_items)
        if vals is not None and ops is not None:
            # Format: [666 == 666] or [1 < 5 < 10]
            parts = [str(vals[0])]
            for i, op in enumerate(ops):
                parts.append(op)
                parts.append(str(vals[i + 1]))
            base += "  [" + " ".join(parts) + "]"
        return base


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
