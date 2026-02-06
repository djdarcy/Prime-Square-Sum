"""
Tests for FunctionRegistry plugin architecture.
"""

import math
import pytest
import tempfile
from pathlib import Path

from utils.function_registry import FunctionRegistry, FunctionSignature, NAMESPACE_PRIORITY


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
            # Qualified keys like "math.pow" have sig.name="pow"
            if '.' in name:
                assert sig.name == name.split('.', 1)[1]
            else:
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
    """Tests for function name collision handling with namespaces."""

    def test_user_overrides_unqualified(self, tmp_path):
        """Test that user function takes unqualified slot, builtin preserved."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        # Unqualified tri -> user version
        assert registry.get("tri")(10) == 30

        # Qualified pss.tri -> original builtin preserved
        assert registry.get("pss.tri")(10) == 55

        # Qualified user.tri -> user version
        assert registry.get("user.tri")(10) == 30

    def test_override_no_warning_with_namespaces(self, tmp_path):
        """Test that namespace collisions don't emit warnings."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")

        registry = FunctionRegistry()

        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("error")
            registry.load_from_file(str(func_file))

    def test_override_source_tracked(self, tmp_path):
        """Test that user function source is tracked in user.* namespace."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        sig = registry.get_signature("user.tri")
        assert sig.source != "builtin"
        assert sig.namespace == "user"


class TestListFunctions:
    """Tests for function listing."""

    def test_list_functions_returns_dict(self):
        """Test that list_functions returns a dictionary."""
        registry = FunctionRegistry()
        result = registry.list_functions()
        assert isinstance(result, dict)
        assert "pss.tri" in result

    def test_list_functions_has_descriptions(self):
        """Test that list_functions includes descriptions."""
        registry = FunctionRegistry()
        result = registry.list_functions()
        # pss.tri has a docstring
        assert len(result["pss.tri"]) > 0

    def test_list_signatures_format(self):
        """Test that list_signatures has proper format."""
        registry = FunctionRegistry()
        result = registry.list_signatures()
        assert isinstance(result, dict)
        # Should have "name(args) - description" format using qualified names
        tri_sig = result["pss.tri"]
        assert "pss.tri(" in tri_sig
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


class TestMathFunctions:
    """Tests for built-in math functions (v0.7.8+)."""

    def test_math_functions_registered(self):
        """Test that all math functions are registered."""
        registry = FunctionRegistry()
        for name in ["pow", "abs", "mod", "sqrt", "floor", "ceil"]:
            assert name in registry, f"{name} not registered"

    def test_pow_integers(self):
        """Test pow() with integer arguments."""
        registry = FunctionRegistry()
        fn = registry.get("pow")
        assert fn(2, 3) == 8
        assert fn(5, 2) == 25
        assert fn(10, 0) == 1

    def test_pow_replaces_square(self):
        """Test pow(x, 2) produces same results as x*x."""
        registry = FunctionRegistry()
        pow_fn = registry.get("pow")
        for x in [0, 1, 5, -3, 100]:
            assert pow_fn(x, 2) == x * x
        # square() is no longer a registered builtin
        assert "square" not in registry

    def test_pow_floats(self):
        """Test pow() with float arguments."""
        registry = FunctionRegistry()
        fn = registry.get("pow")
        assert fn(0.5, 2) == 0.25
        assert abs(fn(2, 0.5) - 1.4142135623730951) < 1e-10

    def test_abs_positive(self):
        """Test abs() with positive input."""
        registry = FunctionRegistry()
        fn = registry.get("abs")
        assert fn(5) == 5
        assert fn(0) == 0

    def test_abs_negative(self):
        """Test abs() with negative input."""
        registry = FunctionRegistry()
        fn = registry.get("abs")
        assert fn(-5) == 5
        assert fn(-3.14) == 3.14

    def test_mod_basic(self):
        """Test mod() basic behavior."""
        registry = FunctionRegistry()
        fn = registry.get("mod")
        assert fn(10, 3) == 1
        assert fn(7, 2) == 1
        assert fn(6, 3) == 0

    def test_mod_division_by_zero(self):
        """Test mod() raises on division by zero."""
        registry = FunctionRegistry()
        fn = registry.get("mod")
        with pytest.raises(ValueError, match="division by zero"):
            fn(5, 0)

    def test_sqrt_perfect_square(self):
        """Test sqrt() returns int for perfect squares."""
        registry = FunctionRegistry()
        fn = registry.get("sqrt")
        assert fn(25) == 5
        assert isinstance(fn(25), int)
        assert fn(0) == 0
        assert fn(1) == 1
        assert fn(144) == 12

    def test_sqrt_non_perfect_square(self):
        """Test sqrt() returns float for non-perfect squares."""
        registry = FunctionRegistry()
        fn = registry.get("sqrt")
        result = fn(2)
        assert isinstance(result, float)
        assert abs(result - 1.4142135623730951) < 1e-10

    def test_sqrt_negative_raises(self):
        """Test sqrt() raises on negative input."""
        registry = FunctionRegistry()
        fn = registry.get("sqrt")
        with pytest.raises(ValueError, match="non-negative"):
            fn(-1)

    def test_floor_basic(self):
        """Test floor() rounds down."""
        registry = FunctionRegistry()
        fn = registry.get("floor")
        assert fn(3.7) == 3
        assert fn(3.0) == 3
        assert fn(-1.5) == -2

    def test_ceil_basic(self):
        """Test ceil() rounds up."""
        registry = FunctionRegistry()
        fn = registry.get("ceil")
        assert fn(3.2) == 4
        assert fn(3.0) == 3
        assert fn(-1.5) == -1

    def test_math_functions_have_metadata(self):
        """Test that math functions have proper signatures."""
        registry = FunctionRegistry()
        for name in ["pow", "abs", "mod", "sqrt", "floor", "ceil"]:
            sig = registry.get_signature(name)
            assert sig.arg_count >= 1, f"{name} should have at least 1 arg"
            assert len(sig.doc) > 0, f"{name} should have a docstring"
            assert sig.source == "builtin"


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


class TestNamespaces:
    """Tests for function namespace system (Issue #46)."""

    def test_math_namespace_qualified(self):
        """math.pow resolves to builtin pow."""
        registry = FunctionRegistry()
        fn = registry.get("math.pow")
        assert fn(2, 10) == 1024

    def test_pss_namespace_qualified(self):
        """pss.tri resolves to builtin tri."""
        registry = FunctionRegistry()
        fn = registry.get("pss.tri")
        assert fn(36) == 666

    def test_unqualified_backward_compat(self):
        """Unqualified names still resolve (backward compat)."""
        registry = FunctionRegistry()
        assert registry.get("pow")(2, 10) == 1024
        assert registry.get("tri")(36) == 666
        assert registry.get("primesum")(7, 2) == 666

    def test_all_pss_builtins_qualified(self):
        """All PSS builtins accessible via pss.* namespace."""
        registry = FunctionRegistry()
        pss_names = [
            "tri", "qtri", "trisum", "is_triangular", "digital_root",
            "nth_prime", "primesum", "fibonacci", "factorial", "catalan",
        ]
        for name in pss_names:
            assert f"pss.{name}" in registry, f"pss.{name} not registered"

    def test_math_module_auto_registered(self):
        """All callable math module functions registered under math.*."""
        registry = FunctionRegistry()
        # Check a representative sample of auto-registered math functions
        for name in ["sin", "cos", "tan", "log", "exp", "gcd"]:
            assert f"math.{name}" in registry, f"math.{name} not registered"

    def test_math_sin_cos_work(self):
        """Auto-registered trig functions produce correct results."""
        registry = FunctionRegistry()
        sin_fn = registry.get("math.sin")
        cos_fn = registry.get("math.cos")
        assert abs(sin_fn(0.0)) < 1e-10
        assert abs(cos_fn(0.0) - 1.0) < 1e-10
        assert abs(sin_fn(math.pi / 2) - 1.0) < 1e-10

    def test_math_log_exp_work(self):
        """Auto-registered log/exp functions produce correct results."""
        registry = FunctionRegistry()
        exp_fn = registry.get("math.exp")
        log_fn = registry.get("math.log")
        assert abs(exp_fn(0) - 1.0) < 1e-10
        assert abs(log_fn(math.e) - 1.0) < 1e-10

    def test_math_gcd_lcm_work(self):
        """Auto-registered gcd/lcm functions produce correct results."""
        registry = FunctionRegistry()
        gcd_fn = registry.get("math.gcd")
        lcm_fn = registry.get("math.lcm")
        assert gcd_fn(12, 8) == 4
        assert lcm_fn(4, 6) == 12

    def test_custom_pow_preserves_int(self):
        """Our custom pow wrapper preserves int (math.pow returns float)."""
        registry = FunctionRegistry()
        result = registry.get("math.pow")(2, 10)
        assert result == 1024
        assert isinstance(result, int)

    def test_custom_sqrt_perfect_square(self):
        """Our custom sqrt returns int for perfect squares."""
        registry = FunctionRegistry()
        result = registry.get("math.sqrt")(25)
        assert result == 5
        assert isinstance(result, int)

    def test_user_namespace_on_load(self, tmp_path):
        """User functions registered under user.* namespace."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def double(x): return x * 2")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        assert "user.double" in registry
        assert "double" in registry
        assert registry.get("user.double")(5) == 10
        assert registry.get("double")(5) == 10

    def test_user_overrides_math(self, tmp_path):
        """User-defined pow takes unqualified slot, math.pow preserved."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def pow(x): return x * x")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        # Unqualified pow -> user version (single arg)
        assert registry.get("pow")(5) == 25
        # Qualified math.pow -> builtin (two args)
        assert registry.get("math.pow")(2, 10) == 1024
        # Qualified user.pow -> user version
        assert registry.get("user.pow")(5) == 25

    def test_user_overrides_pss(self, tmp_path):
        """User-defined tri takes unqualified slot, pss.tri preserved."""
        func_file = tmp_path / "test_funcs.py"
        func_file.write_text("def tri(x): return x * 3")

        registry = FunctionRegistry()
        registry.load_from_file(str(func_file))

        assert registry.get("tri")(10) == 30       # user version
        assert registry.get("pss.tri")(36) == 666  # builtin preserved
        assert registry.get("user.tri")(10) == 30  # user qualified

    def test_namespace_priority_order(self):
        """Verify namespace priority: user > pss > math."""
        assert NAMESPACE_PRIORITY == ["user", "pss", "math"]

    def test_namespace_in_signature(self):
        """FunctionSignature has namespace field populated."""
        registry = FunctionRegistry()
        sig = registry.get_signature("math.pow")
        assert sig.namespace == "math"

        sig2 = registry.get_signature("pss.tri")
        assert sig2.namespace == "pss"

    def test_pss_wins_over_math_for_factorial(self):
        """pss.factorial wins unqualified slot over math.factorial."""
        registry = FunctionRegistry()
        # Unqualified factorial should be pss version
        sig = registry.get_signature("factorial")
        assert sig.namespace == "pss"

        # Both qualified versions exist
        assert "math.factorial" in registry
        assert "pss.factorial" in registry

    def test_unique_count(self):
        """unique_count matches len() and counts each function once."""
        registry = FunctionRegistry()
        count = registry.unique_count()
        assert count == len(registry)
        # Should be significantly less than total keys
        assert count < len(registry._functions)

    def test_list_signatures_shows_qualified(self):
        """list_signatures uses qualified names as keys."""
        registry = FunctionRegistry()
        sigs = registry.list_signatures()
        assert "math.pow" in sigs
        assert "pss.tri" in sigs
        # Unqualified aliases should not appear
        for key in sigs:
            if sigs[key].startswith("pss.") or sigs[key].startswith("math."):
                # Qualified entries have dot in key
                assert '.' in key

    def test_unknown_function_error_shows_unqualified(self):
        """Error message shows unqualified names for readability."""
        registry = FunctionRegistry()
        with pytest.raises(ValueError) as exc_info:
            registry.get("nonexistent")
        # Should show unqualified names like 'tri', 'pow', not 'pss.tri'
        error_msg = str(exc_info.value)
        assert "tri" in error_msg
        assert "pss.tri" not in error_msg
