"""
function_registry.py - Plugin architecture for mathematical functions
=====================================================================

Provides a registry for built-in and user-defined functions that can be
used in expression evaluation. Supports metadata extraction for static
analysis (argument count validation).

Usage:
    from utils.function_registry import FunctionRegistry

    # Create registry with built-in functions
    registry = FunctionRegistry()

    # Get and call a function
    tri = registry.get("tri")
    result = tri(36)  # Returns 666

    # Load user-defined functions
    registry.load_from_file("my_functions.py")

    # Validate argument count before evaluation
    if registry.validate_call("tri", num_args=1):
        # Safe to call

Security Warning:
    The --functions flag executes arbitrary Python code. Only use with
    trusted files. Users run their own code on their own machine.
"""

from dataclasses import dataclass
from typing import Callable, Dict, Optional, Any, List
import inspect
import importlib.util
import warnings
import sys
from pathlib import Path


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


class FunctionRegistry:
    """
    Registry for mathematical functions available in expressions.

    Automatically registers built-in functions on initialization.
    Supports loading user-defined functions from Python files.

    Attributes:
        _functions: Dict mapping function names to FunctionSignature objects
    """

    def __init__(self, register_builtins: bool = True):
        """
        Initialize the function registry.

        Args:
            register_builtins: If True, register built-in functions automatically
        """
        self._functions: Dict[str, FunctionSignature] = {}
        if register_builtins:
            self._register_builtins()

    def _register_builtins(self) -> None:
        """Register built-in mathematical functions."""
        # Import from number_theory
        from utils.number_theory import (
            tri, qtri, trisum, is_triangular, digital_root
        )

        # Import from sieve
        from utils.sieve import nth_prime

        # Import from sequences
        from utils.sequences import primesum, fibonacci, factorial, catalan, square

        # Register each built-in function
        builtins = [
            # Triangular number functions
            ("tri", tri),
            ("qtri", qtri),
            ("trisum", trisum),
            ("is_triangular", is_triangular),
            # Number theory utilities
            ("digital_root", digital_root),
            # Prime functions
            ("nth_prime", nth_prime),
            # Sequence generators
            ("primesum", primesum),
            ("fibonacci", fibonacci),
            ("factorial", factorial),
            ("catalan", catalan),
            # Basic arithmetic
            ("square", square),
        ]

        for name, func in builtins:
            self.register(name, func, source="builtin")

    def register(
        self,
        name: str,
        func: Callable,
        source: str = "builtin"
    ) -> None:
        """
        Register a function with metadata extraction.

        Args:
            name: Name to register the function under
            func: The callable to register
            source: Source identifier ("builtin" or filepath)

        Note:
            If a function with the same name already exists, it will be
            overwritten with a warning.
        """
        if name in self._functions:
            old_source = self._functions[name].source
            warnings.warn(
                f"Function '{name}' from '{old_source}' is being overridden "
                f"by function from '{source}'"
            )

        # Extract signature metadata
        try:
            sig = inspect.signature(func)
            params = list(sig.parameters.values())

            # Count required positional arguments (no default value)
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
            # Fall back to safe defaults
            arg_count = 0
            has_varargs = True
            has_kwargs = False

        # Get docstring
        doc = func.__doc__ or ""
        # Truncate long docstrings for display
        if len(doc) > 200:
            doc = doc[:197] + "..."

        self._functions[name] = FunctionSignature(
            name=name,
            func=func,
            arg_count=arg_count,
            has_varargs=has_varargs,
            has_kwargs=has_kwargs,
            doc=doc,
            source=source
        )

    def get(self, name: str) -> Callable:
        """
        Get a function by name.

        Args:
            name: Function name to look up

        Returns:
            The callable function

        Raises:
            ValueError: If function is not found
        """
        if name not in self._functions:
            available = list(self._functions.keys())
            raise ValueError(
                f"Unknown function: '{name}'. "
                f"Available functions: {', '.join(sorted(available))}"
            )
        return self._functions[name].func

    def get_signature(self, name: str) -> FunctionSignature:
        """
        Get the full signature metadata for a function.

        Args:
            name: Function name to look up

        Returns:
            FunctionSignature with metadata

        Raises:
            ValueError: If function is not found
        """
        if name not in self._functions:
            available = list(self._functions.keys())
            raise ValueError(
                f"Unknown function: '{name}'. "
                f"Available functions: {', '.join(sorted(available))}"
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
        Load user-defined functions from a Python file.

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

        # Register all public callable objects
        count = 0
        for name in dir(module):
            if name.startswith('_'):
                continue

            obj = getattr(module, name)
            if callable(obj) and not inspect.isclass(obj):
                self.register(name, obj, source=filepath)
                count += 1

        return count

    def list_functions(self) -> Dict[str, str]:
        """
        List all registered functions with their descriptions.

        Returns:
            Dict mapping function names to their docstrings (first line)
        """
        result = {}
        for name, sig in sorted(self._functions.items()):
            # Get first line of docstring
            doc = sig.doc.strip().split('\n')[0] if sig.doc else "No description"
            result[name] = doc
        return result

    def list_signatures(self) -> Dict[str, str]:
        """
        List all registered functions with signature info.

        Returns:
            Dict mapping function names to "name(args) - description"
        """
        result = {}
        for name, sig in sorted(self._functions.items()):
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

    def __contains__(self, name: str) -> bool:
        """Check if a function is registered."""
        return name in self._functions

    def __len__(self) -> int:
        """Return number of registered functions."""
        return len(self._functions)

    def names(self) -> List[str]:
        """Return list of all registered function names."""
        return list(self._functions.keys())
