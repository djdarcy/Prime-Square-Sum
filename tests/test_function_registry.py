"""
Tests for FunctionRegistry plugin architecture.
"""

import pytest
import tempfile
from pathlib import Path

from utils.function_registry import FunctionRegistry, FunctionSignature


class TestFunctionSignature:
    """Tests for FunctionSignature dataclass."""

    def test_dataclass_creation(self):
        """Test creating a FunctionSignature."""
        sig = FunctionSignature(
            name="test",
            func=lambda x: x,
            arg_count=1,
            has_varargs=False,
            doc="Test function",
            source="test"
        )
        assert sig.name == "test"
        assert sig.arg_count == 1
        assert sig.has_varargs is False
        assert sig.doc == "Test function"
        assert sig.source == "test"

    def test_dataclass_defaults(self):
        """Test FunctionSignature default values."""
        sig = FunctionSignature(
            name="test",
            func=lambda x: x,
            arg_count=1
        )
        assert sig.has_varargs is False
        assert sig.has_kwargs is False
        assert sig.doc == ""
        assert sig.source == "builtin"


class TestBuiltinRegistration:
    """Tests for built-in function registration."""

    def test_builtins_registered_on_init(self):
        """Test that built-in functions are registered automatically."""
        registry = FunctionRegistry()

        # Check expected built-ins are present
        assert "tri" in registry
        assert "qtri" in registry
        assert "trisum" in registry
        assert "is_triangular" in registry
        assert "digital_root" in registry
        assert "nth_prime" in registry

    def test_builtin_count(self):
        """Test number of built-in functions."""
        registry = FunctionRegistry()
        # At minimum, we should have these 6 built-ins
        assert len(registry) >= 6

    def test_skip_builtins(self):
        """Test creating registry without built-ins."""
        registry = FunctionRegistry(register_builtins=False)
        assert len(registry) == 0
        assert "tri" not in registry

    def test_tri_function_works(self):
        """Test that tri() can be retrieved and called."""
        registry = FunctionRegistry()
        tri = registry.get("tri")
        assert tri(4) == 10
        assert tri(36) == 666

    def test_qtri_function_works(self):
        """Test that qtri() can be retrieved and called."""
        registry = FunctionRegistry()
        qtri = registry.get("qtri")
        assert qtri(10) == 4
        assert qtri(666) == 36
        assert qtri(5) is None

    def test_trisum_function_works(self):
        """Test that trisum() can be retrieved and called."""
        registry = FunctionRegistry()
        trisum = registry.get("trisum")
        assert trisum(10) == 666

    def test_is_triangular_function_works(self):
        """Test that is_triangular() can be retrieved and called."""
        registry = FunctionRegistry()
        is_triangular = registry.get("is_triangular")
        assert is_triangular(666) is True
        assert is_triangular(667) is False

    def test_digital_root_function_works(self):
        """Test that digital_root() can be retrieved and called."""
        registry = FunctionRegistry()
        digital_root = registry.get("digital_root")
        assert digital_root(666) == 9
        assert digital_root(38) == 2

    def test_nth_prime_function_works(self):
        """Test that nth_prime() can be retrieved and called."""
        registry = FunctionRegistry()
        nth_prime = registry.get("nth_prime")
        assert nth_prime(1) == 2
        assert nth_prime(7) == 17


class TestFunctionMetadata:
    """Tests for function metadata extraction."""

    def test_tri_signature(self):
        """Test tri() signature metadata."""
        registry = FunctionRegistry()
        sig = registry.get_signature("tri")
        assert sig.name == "tri"
        assert sig.arg_count == 1
        assert sig.has_varargs is False
        assert sig.source == "builtin"
        assert len(sig.doc) > 0  # Has docstring

    def test_all_builtins_have_metadata(self):
        """Test that all built-ins have proper metadata."""
        registry = FunctionRegistry()
        for name in registry.names():
            sig = registry.get_signature(name)
            assert sig.name == name
            assert sig.arg_count >= 0
            assert sig.source == "builtin"


class TestArgumentValidation:
    """Tests for argument count validation."""

    def test_validate_call_correct_args(self):
        """Test validation passes with correct arg count."""
        registry = FunctionRegistry()
        # tri(n) takes 1 argument
        assert registry.validate_call("tri", 1) is True

    def test_validate_call_too_few_args(self):
        """Test validation fails with too few arguments."""
        registry = FunctionRegistry()
        # tri(n) takes 1 argument
        assert registry.validate_call("tri", 0) is False

    def test_get_validation_error_message(self):
        """Test error message generation."""
        registry = FunctionRegistry()
        error = registry.get_validation_error("tri", 0)
        assert error is not None
        assert "tri()" in error
        assert "1" in error  # expected count
        assert "0" in error  # actual count

    def test_get_validation_error_none_when_valid(self):
        """Test no error message when valid."""
        registry = FunctionRegistry()
        error = registry.get_validation_error("tri", 1)
        assert error is None


class TestUnknownFunction:
    """Tests for unknown function handling."""

    def test_get_unknown_raises(self):
        """Test that getting unknown function raises ValueError."""
        registry = FunctionRegistry()
        with pytest.raises(ValueError, match="Unknown function"):
            registry.get("nonexistent")

    def test_get_unknown_shows_available(self):
        """Test that error message shows available functions."""
        registry = FunctionRegistry()
        with pytest.raises(ValueError) as exc_info:
            registry.get("nonexistent")
        assert "tri" in str(exc_info.value)

    def test_get_signature_unknown_raises(self):
        """Test that getting unknown signature raises ValueError."""
        registry = FunctionRegistry()
        with pytest.raises(ValueError, match="Unknown function"):
            registry.get_signature("nonexistent")


class TestUserFunctionLoading:
    """Tests for loading user-defined functions."""

    def test_load_simple_function(self, tmp_path):
        """Test loading a simple function from file."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def double(x): return x * 2")

        registry = FunctionRegistry()
        count = registry.load_from_file(str(func_file))

        assert count == 1
        assert "double" in registry
        assert registry.get("double")(5) == 10

    def test_load_multiple_functions(self, tmp_path):
        """Test loading multiple functions from file."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("""
def add(a, b):
    return a + b

def multiply(a, b):
    return a * b

def square(x):
    return x * x
""")

        registry = FunctionRegistry()
        count = registry.load_from_file(str(func_file))

        assert count == 3
        assert "add" in registry
        assert "multiply" in registry
        assert "square" in registry
        assert registry.get("add")(2, 3) == 5
        assert registry.get("multiply")(4, 5) == 20
        assert registry.get("square")(7) == 49

    def test_load_skips_private_functions(self, tmp_path):
        """Test that private functions (starting with _) are skipped."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("""
def public_func(x):
    return x

def _private_func(x):
    return x

def __dunder_func(x):
    return x
""")

        registry = FunctionRegistry()
        count = registry.load_from_file(str(func_file))

        assert count == 1
        assert "public_func" in registry
        assert "_private_func" not in registry
        assert "__dunder_func" not in registry

    def test_load_skips_classes(self, tmp_path):
        """Test that classes are not registered as functions."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("""
def my_func(x):
    return x

class MyClass:
    pass
""")

        registry = FunctionRegistry()
        count = registry.load_from_file(str(func_file))

        assert count == 1
        assert "my_func" in registry
        assert "MyClass" not in registry

    def test_load_file_not_found(self):
        """Test error when file doesn't exist."""
        registry = FunctionRegistry()
        with pytest.raises(FileNotFoundError):
            registry.load_from_file("/nonexistent/path/funcs.py")

    def test_load_non_python_file(self, tmp_path):
        """Test error when file is not .py."""
        text_file = tmp_path / "funcs.txt"
        text_file.write_text("not python")

        registry = FunctionRegistry()
        with pytest.raises(ValueError, match="must be a .py file"):
            registry.load_from_file(str(text_file))

    def test_function_with_docstring(self, tmp_path):
        """Test that docstrings are extracted from user functions."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text('''
def documented_func(x):
    """This is my documentation."""
    return x
''')

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("documented_func")
        assert "documentation" in sig.doc

    def test_user_function_source_tracked(self, tmp_path):
        """Test that user function source is tracked."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def my_func(x): return x")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("my_func")
        assert str(func_file) in sig.source


class TestFunctionOverride:
    """Tests for function name collision handling."""

    def test_override_builtin_with_warning(self, tmp_path):
        """Test that overriding a built-in generates a warning."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")  # Override tri

        registry = FunctionRegistry()

        with pytest.warns(UserWarning, match="being overridden"):
            registry.load_from_file(str(func_file))

        # The user function should now be active
        assert registry.get("tri")(10) == 30  # Not tri(10)=55

    def test_override_source_updated(self, tmp_path):
        """Test that override updates the source."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")

        registry = FunctionRegistry()

        with pytest.warns(UserWarning):
            registry.load_from_file(str(func_file))

        sig = registry.get_signature("tri")
        assert sig.source != "builtin"


class TestListFunctions:
    """Tests for function listing."""

    def test_list_functions_returns_dict(self):
        """Test that list_functions returns a dictionary."""
        registry = FunctionRegistry()
        result = registry.list_functions()
        assert isinstance(result, dict)
        assert "tri" in result

    def test_list_functions_has_descriptions(self):
        """Test that list_functions includes descriptions."""
        registry = FunctionRegistry()
        result = registry.list_functions()
        # tri has a docstring
        assert len(result["tri"]) > 0

    def test_list_signatures_format(self):
        """Test that list_signatures has proper format."""
        registry = FunctionRegistry()
        result = registry.list_signatures()
        assert isinstance(result, dict)
        # Should have "name(args) - description" format
        tri_sig = result["tri"]
        assert "tri(" in tri_sig
        assert ")" in tri_sig
        assert " - " in tri_sig


class TestContainerProtocol:
    """Tests for container-like behavior."""

    def test_contains(self):
        """Test 'in' operator."""
        registry = FunctionRegistry()
        assert "tri" in registry
        assert "nonexistent" not in registry

    def test_len(self):
        """Test len() function."""
        registry = FunctionRegistry()
        assert len(registry) >= 6  # At least the built-ins

    def test_names(self):
        """Test names() method."""
        registry = FunctionRegistry()
        names = registry.names()
        assert isinstance(names, list)
        assert "tri" in names
        assert "qtri" in names


class TestEdgeCases:
    """Tests for edge cases."""

    def test_function_with_varargs(self, tmp_path):
        """Test function with *args."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def varargs_func(*args): return sum(args)")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("varargs_func")
        assert sig.has_varargs is True
        assert registry.get("varargs_func")(1, 2, 3, 4) == 10

    def test_function_with_kwargs(self, tmp_path):
        """Test function with **kwargs."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def kwargs_func(**kwargs): return len(kwargs)")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("kwargs_func")
        assert sig.has_kwargs is True

    def test_function_with_defaults(self, tmp_path):
        """Test function with default arguments."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def with_default(a, b=10): return a + b")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("with_default")
        # Only required args counted
        assert sig.arg_count == 1

        # Should work with 1 or 2 args
        func = registry.get("with_default")
        assert func(5) == 15
        assert func(5, 20) == 25

    def test_empty_file(self, tmp_path):
        """Test loading empty file."""
        func_file = tmp_path / "empty.py"
        func_file.write_text("")

        registry = FunctionRegistry()
        count = registry.load_from_file(str(func_file))

        assert count == 0

    def test_file_with_syntax_error(self, tmp_path):
        """Test loading file with syntax error."""
        func_file = tmp_path / "bad_syntax.py"
        func_file.write_text("def broken(: return")

        registry = FunctionRegistry()
        with pytest.raises(ImportError):
            registry.load_from_file(str(func_file))
