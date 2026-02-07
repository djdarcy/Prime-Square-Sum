"""
function_registry.py - Plugin architecture for mathematical functions
=====================================================================

Provides a namespaced registry for built-in and user-defined functions
that can be used in expression evaluation. Functions are organized into
three namespaces:

    math.*  — Python math module functions (sin, cos, pow, sqrt, etc.)
    pss.*   — Prime-Square-Sum tool functions (tri, primesum, fibonacci, etc.)
    user.*  — User-defined functions loaded via --functions

Unqualified names resolve by priority: user > pss > math.
Qualified names (e.g., math.pow, pss.tri) always resolve directly.

Usage:
    from utils.function_registry import FunctionRegistry

    # Create registry with built-in functions
    registry = FunctionRegistry()

    # Get function by qualified or unqualified name
    tri = registry.get("tri")           # pss.tri (unqualified)
    tri = registry.get("pss.tri")       # pss.tri (qualified)
    sin = registry.get("math.sin")      # math.sin (qualified)

    # Load user-defined functions (registered under user.*)
    registry.load_from_file("my_functions.py")

Security Warning:
    The --functions flag executes arbitrary Python code. Only use with
    trusted files. Users run their own code on their own machine.
"""

from dataclasses import dataclass, field
from typing import Callable, Dict, Optional, Any, List, Union
import inspect
import importlib.util
import math as _math
import warnings
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Math function wrappers
# ---------------------------------------------------------------------------
# Custom wrappers that provide better behavior than the raw math module
# equivalents for this tool's use cases (int preservation, error messages).

def _builtin_pow(base: Union[int, float], exp: Union[int, float]) -> Union[int, float]:
    """Raise base to the power of exp."""
    return base ** exp


def _builtin_abs(x: Union[int, float]) -> Union[int, float]:
    """Return the absolute value of x."""
    return abs(x)


def _builtin_mod(a: Union[int, float], b: Union[int, float]) -> Union[int, float]:
    """Return a modulo b (remainder of a / b)."""
    if b == 0:
        raise ValueError("mod() division by zero")
    return a % b


def _builtin_sqrt(x: Union[int, float]) -> Union[int, float]:
    """Return the square root of x. Returns int if result is integral."""
    if x < 0:
        raise ValueError(f"sqrt() requires non-negative input, got {x}")
    result = _math.isqrt(x) if isinstance(x, int) else _math.sqrt(x)
    # For integer inputs, isqrt returns exact int; verify it's a perfect square
    if isinstance(x, int):
        if result * result == x:
            return result
        # Not a perfect square - return float
        return _math.sqrt(x)
    return result


def _builtin_floor(x: Union[int, float]) -> int:
    """Round x down to the nearest integer."""
    return _math.floor(x)


def _builtin_ceil(x: Union[int, float]) -> int:
    """Round x up to the nearest integer."""
    return _math.ceil(x)


@dataclass
class FunctionSignature:
    """Metadata about a registered function."""
    name: str
    func: Callable
    arg_count: int  # Number of required positional arguments
    has_varargs: bool = False  # Has *args
    has_kwargs: bool = False  # Has **kwargs
    doc: str = ""
    source: str = "builtin"  # "builtin" or filepath
    namespace: str = ""  # "math", "pss", "user", or "" for legacy


# Namespace resolution priority (lower index = higher priority)
NAMESPACE_PRIORITY = ["user", "pss", "math"]


class FunctionRegistry:
    """
    Namespaced registry for mathematical functions available in expressions.

    Functions are registered under both a qualified name (namespace.name)
    and an unqualified name (name). Unqualified lookups resolve by
    namespace priority: user > pss > math.

    Attributes:
        _functions: Dict mapping function names to FunctionSignature objects.
            Contains both qualified keys ("math.pow") and unqualified
            aliases ("pow") pointing to the highest-priority version.
        _unqualified_owners: Dict tracking which namespaces claim each
            unqualified name, ordered by priority.
    """

    def __init__(self, register_builtins: bool = True):
        """
        Initialize the function registry.

        Args:
            register_builtins: If True, register built-in functions automatically
        """
        self._functions: Dict[str, FunctionSignature] = {}
        self._unqualified_owners: Dict[str, List[str]] = {}
        if register_builtins:
            self._register_builtins()

    def _build_signature(
        self,
        name: str,
        func: Callable,
        source: str,
        namespace: str = ""
    ) -> FunctionSignature:
        """Build FunctionSignature with metadata extraction."""
        try:
            sig = inspect.signature(func)
            params = list(sig.parameters.values())

            arg_count = sum(
                1 for p in params
                if p.default is inspect.Parameter.empty
                and p.kind in (
                    inspect.Parameter.POSITIONAL_ONLY,
                    inspect.Parameter.POSITIONAL_OR_KEYWORD
                )
            )

            has_varargs = any(
                p.kind == inspect.Parameter.VAR_POSITIONAL for p in params
            )
            has_kwargs = any(
                p.kind == inspect.Parameter.VAR_KEYWORD for p in params
            )

        except (ValueError, TypeError):
            # Some built-in functions don't support inspect.signature
            arg_count = 0
            has_varargs = True
            has_kwargs = False

        doc = func.__doc__ or ""
        if len(doc) > 200:
            doc = doc[:197] + "..."

        return FunctionSignature(
            name=name,
            func=func,
            arg_count=arg_count,
            has_varargs=has_varargs,
            has_kwargs=has_kwargs,
            doc=doc,
            source=source,
            namespace=namespace,
        )

    def _namespace_index(self, namespace: str) -> int:
        """Get priority index for a namespace (lower = higher priority)."""
        try:
            return NAMESPACE_PRIORITY.index(namespace)
        except ValueError:
            return len(NAMESPACE_PRIORITY)

    def _register_namespaced(
        self,
        name: str,
        func: Callable,
        namespace: str,
        source: str = "builtin"
    ) -> None:
        """
        Register a function under both qualified and unqualified names.

        The qualified name (namespace.name) is always registered.
        The unqualified name goes to the highest-priority namespace.

        Args:
            name: Unqualified function name (e.g., "pow")
            func: The callable to register
            namespace: Namespace identifier ("math", "pss", "user")
            source: Source identifier ("builtin" or filepath)
        """
        qualified_name = f"{namespace}.{name}"
        sig = self._build_signature(name, func, source, namespace)

        # Always register under qualified name
        self._functions[qualified_name] = sig

        # Handle unqualified name based on priority
        new_priority = self._namespace_index(namespace)

        if name in self._unqualified_owners:
            existing_ns = self._unqualified_owners[name][0]
            existing_priority = self._namespace_index(existing_ns)

            if new_priority <= existing_priority:
                # New namespace has equal or higher priority — take the slot
                self._functions[name] = sig
                # Move to front of owners list
                if namespace in self._unqualified_owners[name]:
                    self._unqualified_owners[name].remove(namespace)
                self._unqualified_owners[name].insert(0, namespace)
            else:
                # Lower priority — only qualified name registered
                if namespace not in self._unqualified_owners[name]:
                    self._unqualified_owners[name].append(namespace)
        else:
            # First registration of this unqualified name
            self._functions[name] = sig
            self._unqualified_owners[name] = [namespace]

    def _register_builtins(self) -> None:
        """Register built-in functions under math.*, pss.*, and bitwise namespaces."""
        self._register_pss_builtins()
        self._register_math_builtins()
        self._register_bitwise_builtins()

    def _register_bitwise_builtins(self) -> None:
        """Register bitwise compound functions (nand, nor, xnor)."""
        def nand(a: int, b: int) -> int:
            """Bitwise NAND: ~(a & b)"""
            return ~(int(a) & int(b))

        def nor(a: int, b: int) -> int:
            """Bitwise NOR: ~(a | b)"""
            return ~(int(a) | int(b))

        def xnor(a: int, b: int) -> int:
            """Bitwise XNOR: ~(a ^ b)"""
            return ~(int(a) ^ int(b))

        for name, func in [("nand", nand), ("nor", nor), ("xnor", xnor)]:
            self._register_namespaced(name, func, namespace="pss", source="builtin")

    def _register_pss_builtins(self) -> None:
        """Register Prime-Square-Sum specific functions under pss.* namespace."""
        from utils.number_theory import (
            tri, qtri, trisum, is_triangular, digital_root
        )
        from utils.sieve import nth_prime
        from utils.sequences import primesum, fibonacci, factorial, catalan

        pss_builtins = [
            ("tri", tri),
            ("qtri", qtri),
            ("trisum", trisum),
            ("is_triangular", is_triangular),
            ("digital_root", digital_root),
            ("nth_prime", nth_prime),
            ("primesum", primesum),
            ("fibonacci", fibonacci),
            ("factorial", factorial),
            ("catalan", catalan),
        ]

        for name, func in pss_builtins:
            self._register_namespaced(name, func, namespace="pss", source="builtin")

    def _register_math_builtins(self) -> None:
        """Register math functions under math.* namespace.

        Auto-registers all callable functions from Python's math module,
        then overrides specific entries with custom wrappers that provide
        better behavior for this tool (int preservation, error messages).
        """
        # Step 1: Auto-register all math module functions
        for name in sorted(dir(_math)):
            if name.startswith('_'):
                continue
            obj = getattr(_math, name)
            if callable(obj):
                self._register_namespaced(name, obj, namespace="math", source="builtin")

        # Step 2: Override with custom wrappers for better tool behavior
        # - pow: uses ** operator (preserves int, math.pow always returns float)
        # - sqrt: perfect-square detection returns int
        # - floor/ceil: thin wrappers with proper signatures
        custom_overrides = [
            ("pow", _builtin_pow),
            ("sqrt", _builtin_sqrt),
            ("floor", _builtin_floor),
            ("ceil", _builtin_ceil),
        ]
        for name, func in custom_overrides:
            self._register_namespaced(name, func, namespace="math", source="builtin")

        # Step 3: Additional math utilities not in Python's math module
        custom_extras = [
            ("abs", _builtin_abs),   # Python builtin abs()
            ("mod", _builtin_mod),   # Modulo operator with zero-check
        ]
        for name, func in custom_extras:
            self._register_namespaced(name, func, namespace="math", source="builtin")

    def register(
        self,
        name: str,
        func: Callable,
        source: str = "builtin",
        namespace: str = "",
    ) -> None:
        """
        Register a function with metadata extraction.

        If namespace is provided, uses dual registration (qualified +
        unqualified with priority). Otherwise falls back to flat
        registration for backward compatibility.

        Args:
            name: Name to register the function under
            func: The callable to register
            source: Source identifier ("builtin" or filepath)
            namespace: Namespace identifier ("math", "pss", "user", or "")
        """
        if namespace:
            self._register_namespaced(name, func, namespace=namespace, source=source)
            return

        # Legacy flat registration (backward compat for tests/direct calls)
        if name in self._functions:
            old_source = self._functions[name].source
            warnings.warn(
                f"Function '{name}' from '{old_source}' is being overridden "
                f"by function from '{source}'"
            )

        self._functions[name] = self._build_signature(name, func, source, namespace)

    def get(self, name: str) -> Callable:
        """
        Get a function by name (qualified or unqualified).

        Qualified names (e.g., "math.pow") resolve directly.
        Unqualified names (e.g., "pow") resolve by priority: user > pss > math.

        Args:
            name: Function name to look up

        Returns:
            The callable function

        Raises:
            ValueError: If function is not found
        """
        if name not in self._functions:
            # Show unqualified names for readability in error message
            available = sorted(set(
                k for k in self._functions.keys()
                if '.' not in k
            ))
            raise ValueError(
                f"Unknown function: '{name}'. "
                f"Available functions: {', '.join(available)}"
            )
        return self._functions[name].func

    def get_signature(self, name: str) -> FunctionSignature:
        """
        Get the full signature metadata for a function.

        Args:
            name: Function name to look up (qualified or unqualified)

        Returns:
            FunctionSignature with metadata

        Raises:
            ValueError: If function is not found
        """
        if name not in self._functions:
            available = sorted(set(
                k for k in self._functions.keys()
                if '.' not in k
            ))
            raise ValueError(
                f"Unknown function: '{name}'. "
                f"Available functions: {', '.join(available)}"
            )
        return self._functions[name]

    def validate_call(self, name: str, num_args: int) -> bool:
        """
        Validate that a function call has the correct number of arguments.

        Args:
            name: Function name
            num_args: Number of arguments being passed

        Returns:
            True if valid, False if invalid

        Raises:
            ValueError: If function is not found
        """
        sig = self.get_signature(name)

        # If function accepts varargs, any number of args is valid
        if sig.has_varargs:
            return num_args >= sig.arg_count

        # Otherwise, must match exactly (for required args)
        return num_args >= sig.arg_count

    def get_validation_error(self, name: str, num_args: int) -> Optional[str]:
        """
        Get a descriptive error message if argument count is invalid.

        Args:
            name: Function name
            num_args: Number of arguments being passed

        Returns:
            Error message string, or None if valid
        """
        sig = self.get_signature(name)

        if sig.has_varargs:
            if num_args < sig.arg_count:
                return (
                    f"{name}() requires at least {sig.arg_count} argument(s), "
                    f"got {num_args}"
                )
        else:
            if num_args < sig.arg_count:
                return (
                    f"{name}() requires {sig.arg_count} argument(s), "
                    f"got {num_args}"
                )

        return None

    def load_from_file(self, filepath: str) -> int:
        """
        Load user-defined functions from a Python file under user.* namespace.

        WARNING: This executes arbitrary Python code. Only use with trusted files.

        Args:
            filepath: Path to Python file containing function definitions

        Returns:
            Number of functions loaded

        Raises:
            FileNotFoundError: If file doesn't exist
            ImportError: If file cannot be imported
        """
        path = Path(filepath)
        if not path.exists():
            raise FileNotFoundError(f"Function file not found: {filepath}")

        if not path.suffix == '.py':
            raise ValueError(f"Function file must be a .py file: {filepath}")

        # Load the module dynamically
        module_name = f"user_functions_{path.stem}"
        spec = importlib.util.spec_from_file_location(module_name, filepath)

        if spec is None or spec.loader is None:
            raise ImportError(f"Cannot load module from: {filepath}")

        module = importlib.util.module_from_spec(spec)

        # Add to sys.modules temporarily so relative imports work
        sys.modules[module_name] = module

        try:
            spec.loader.exec_module(module)
        except Exception as e:
            del sys.modules[module_name]
            raise ImportError(f"Error loading {filepath}: {e}") from e

        # Register all public callable objects under user.* namespace
        count = 0
        for name in dir(module):
            if name.startswith('_'):
                continue

            obj = getattr(module, name)
            if callable(obj) and not inspect.isclass(obj):
                self._register_namespaced(name, obj, namespace="user", source=filepath)
                count += 1

        return count

    def list_functions(self) -> Dict[str, str]:
        """
        List all registered functions with their descriptions.

        Returns only qualified names to avoid duplicates.

        Returns:
            Dict mapping qualified function names to their docstrings (first line)
        """
        result = {}
        for name, sig in sorted(self._functions.items()):
            # Skip unqualified aliases — only show qualified names
            if '.' not in name and sig.namespace:
                continue
            doc = sig.doc.strip().split('\n')[0] if sig.doc else "No description"
            result[name] = doc
        return result

    def list_signatures(self) -> Dict[str, str]:
        """
        List all registered functions with signature info.

        Returns only qualified names to avoid duplicates.

        Returns:
            Dict mapping qualified function names to "name(args) - description"
        """
        result = {}
        for name, sig in sorted(self._functions.items()):
            # Skip unqualified aliases — only show qualified names
            if '.' not in name and sig.namespace:
                continue

            # Build argument representation
            if sig.has_varargs:
                args = f"arg1, ..., argN" if sig.arg_count == 0 else f"x1..x{sig.arg_count}, ..."
            elif sig.arg_count == 0:
                args = ""
            elif sig.arg_count == 1:
                args = "x"
            else:
                args = ", ".join(f"x{i+1}" for i in range(sig.arg_count))

            # Get first line of docstring
            doc = sig.doc.strip().split('\n')[0] if sig.doc else "No description"

            result[name] = f"{name}({args}) - {doc}"

        return result

    def unique_count(self) -> int:
        """Return count of unique functions (each counted once, not aliases)."""
        # Count qualified entries (each function has exactly one qualified entry)
        qualified = sum(1 for k in self._functions if '.' in k)
        # Plus any functions without a namespace
        no_ns = sum(
            1 for k, sig in self._functions.items()
            if '.' not in k and not sig.namespace
        )
        return qualified + no_ns

    def __contains__(self, name: str) -> bool:
        """Check if a function is registered (qualified or unqualified)."""
        return name in self._functions

    def __len__(self) -> int:
        """Return number of unique registered functions."""
        return self.unique_count()

    def list_compact(self) -> Dict[str, List[str]]:
        """Return short function names grouped by namespace.

        Returns:
            Dict mapping namespace to sorted list of unqualified names.
        """
        groups: Dict[str, List[str]] = {}
        for key, sig in self._functions.items():
            if '.' not in key:
                continue
            ns, short = key.split('.', 1)
            groups.setdefault(ns, []).append(short)
        for names in groups.values():
            names.sort()
        return groups

    def names(self) -> List[str]:
        """Return list of all registered function names (both qualified and unqualified)."""
        return list(self._functions.keys())
