"""
Tests for CLI utilities and expression building.

Issues: #18 (CLI rewrite), #21 (Saved Equations), #22 (Configuration)
Epic: #13 (Generalized Expression Grammar)
"""

import pytest
import json
import tempfile
from pathlib import Path
from argparse import Namespace
from utils.cli import (
    ExpressionComponents,
    build_expression_from_args,
    build_bounds_from_args,
    format_match,
    format_no_match,
    DEFAULTS,
    DEFAULT_BOUNDS,
    # Issue #21: Equation loading
    SavedEquation,
    EquationsFile,
    ParameterDef,
    load_equations_file,
    parse_var_string,
    # Issue #22: Configuration
    Config,
    load_config,
    resolve_default_equation,
    # Issue #63: Dynamic help text
    resolve_effective_defaults,
    # Issue #37: Iterator definitions
    IteratorDef,
    parse_iterator_def,
    build_iterator_factories_from_args,
)


# =============================================================================
# ExpressionComponents Tests
# =============================================================================

class TestExpressionComponents:
    """Test ExpressionComponents dataclass."""

    def test_defaults(self):
        """Check default values match expected."""
        comp = ExpressionComponents()
        assert comp.quantifier == "does_exist"
        assert comp.lhs == "primesum(n,2)"
        assert comp.operator == "=="
        assert comp.rhs is None

    def test_to_expression_with_rhs(self):
        """to_expression builds correct string when RHS provided."""
        comp = ExpressionComponents(rhs="666")
        assert comp.to_expression() == "does_exist primesum(n,2) == 666"

    def test_to_expression_custom_lhs(self):
        """to_expression with custom LHS."""
        comp = ExpressionComponents(lhs="primesum(n,3)", rhs="666")
        assert comp.to_expression() == "does_exist primesum(n,3) == 666"

    def test_to_expression_custom_quantifier(self):
        """to_expression with for_any quantifier."""
        comp = ExpressionComponents(quantifier="for_any", rhs="tri(m)")
        assert comp.to_expression() == "for_any primesum(n,2) == tri(m)"

    def test_to_expression_custom_operator(self):
        """to_expression with different operator."""
        comp = ExpressionComponents(operator=">=", rhs="100")
        assert comp.to_expression() == "does_exist primesum(n,2) >= 100"

    def test_to_expression_raises_without_rhs(self):
        """to_expression raises ValueError without RHS."""
        comp = ExpressionComponents()
        with pytest.raises(ValueError, match="RHS"):
            comp.to_expression()

    def test_fully_custom(self):
        """to_expression with all custom values."""
        comp = ExpressionComponents(
            quantifier="for_any",
            lhs="tri(n)",
            operator="!=",
            rhs="primesum(m,2)"
        )
        assert comp.to_expression() == "for_any tri(n) != primesum(m,2)"


# =============================================================================
# build_expression_from_args Tests
# =============================================================================

class TestBuildExpressionFromArgs:
    """Test expression building from CLI arguments."""

    def test_tier1_expr_takes_precedence(self):
        """--expr flag takes precedence over everything."""
        args = Namespace(
            expr="for_any tri(n) == 666",
            equation=None,
            lhs="ignored",
            rhs="ignored",
            operator="!=",
            quantifier="for_any",
        )
        assert build_expression_from_args(args) == "for_any tri(n) == 666"

    def test_tier2_decomposed_simple(self):
        """Decomposed flags with only --rhs."""
        args = Namespace(
            expr=None,
            equation=None,
            lhs=None,
            rhs="666",
            operator=None,
            quantifier=None,
        )
        assert build_expression_from_args(args) == "does_exist primesum(n,2) == 666"

    def test_tier2_decomposed_custom_lhs(self):
        """Decomposed flags with custom --lhs."""
        args = Namespace(
            expr=None,
            equation=None,
            lhs="primesum(n,3)",
            rhs="666",
            operator=None,
            quantifier=None,
        )
        assert build_expression_from_args(args) == "does_exist primesum(n,3) == 666"

    def test_tier2_decomposed_all_flags(self):
        """Decomposed flags with all options."""
        args = Namespace(
            expr=None,
            equation=None,
            lhs="tri(n)",
            rhs="primesum(m,2)",
            operator="<=",
            quantifier="for_any",
        )
        assert build_expression_from_args(args) == "for_any tri(n) <= primesum(m,2)"

    def test_tier3_equation_loads_from_file(self):
        """--equation loads equation from equations.json (Issue #21)."""
        args = Namespace(
            expr=None,
            equation="1",
            lhs=None,
            rhs="666",
            operator=None,
            quantifier=None,
            var=None,
        )
        # This should work now that Issue #21 is implemented
        result = build_expression_from_args(args)
        # primesum-squared with a=2 default
        assert "primesum(n,2)" in result
        assert "666" in result

    def test_missing_rhs_raises_error(self):
        """Missing RHS raises ValueError."""
        args = Namespace(
            expr=None,
            equation=None,
            lhs="tri(n)",
            rhs=None,
            operator=None,
            quantifier=None,
        )
        with pytest.raises(ValueError, match="RHS"):
            build_expression_from_args(args)


# =============================================================================
# build_bounds_from_args Tests
# =============================================================================

class TestBuildBoundsFromArgs:
    """Test bounds building from CLI arguments."""

    def test_defaults_applied(self):
        """Default bounds applied when not specified."""
        args = Namespace()
        bounds = build_bounds_from_args(args, "does_exist primesum(n,2) == 666")
        assert bounds['n'] == DEFAULT_BOUNDS['n']
        assert bounds['m'] == DEFAULT_BOUNDS['m']

    def test_explicit_max_n(self):
        """--max n:VALUE overrides default."""
        args = Namespace(iter_stop=['n:5000'])
        bounds = build_bounds_from_args(args, "does_exist primesum(n,2) == 666")
        assert bounds['n'] == 5000
        assert bounds['m'] == DEFAULT_BOUNDS['m']

    def test_explicit_max_m(self):
        """--max m:VALUE overrides default."""
        args = Namespace(iter_stop=['m:500'])
        bounds = build_bounds_from_args(args, "does_exist primesum(n,2) == 666")
        assert bounds['n'] == DEFAULT_BOUNDS['n']
        assert bounds['m'] == 500

    def test_both_explicit(self):
        """Both bounds can be explicit."""
        args = Namespace(iter_stop=['n:1000', 'm:100'])
        bounds = build_bounds_from_args(args, "for_any primesum(n,2) == tri(m)")
        assert bounds['n'] == 1000
        assert bounds['m'] == 100

    def test_max_arbitrary_variable(self):
        """--max VAR:VALUE works for variables beyond n and m."""
        args = Namespace(iter_stop=['k:500'])
        bounds = build_bounds_from_args(args, "does_exist f(k) == 42")
        assert bounds['k'] == 500

    def test_max_multiple(self):
        """Multiple --max flags append correctly."""
        args = Namespace(iter_stop=['n:5000', 'm:200'])
        bounds = build_bounds_from_args(args, "for_any primesum(n,2) == tri(m)")
        assert bounds['n'] == 5000
        assert bounds['m'] == 200


# =============================================================================
# Output Formatting Tests
# =============================================================================

class TestFormatMatch:
    """Test match result formatting."""

    def test_text_format_single_var(self):
        """Text format with single variable."""
        result = format_match({'n': 7}, 'text')
        assert result == "Found: n=7"

    def test_text_format_multiple_vars(self):
        """Text format with multiple variables."""
        result = format_match({'m': 36, 'n': 7}, 'text')
        # Should be sorted alphabetically
        assert result == "Found: m=36, n=7"

    def test_text_format_empty(self):
        """Text format with no variables."""
        result = format_match({}, 'text')
        assert result == "Found: (no variables)"

    def test_json_format(self):
        """JSON format output."""
        result = format_match({'n': 7}, 'json')
        parsed = json.loads(result)
        assert parsed['found'] is True
        assert parsed['variables'] == {'n': 7}

    def test_csv_format_single_var(self):
        """CSV format with single variable."""
        result = format_match({'n': 7}, 'csv')
        assert result == "n=7"

    def test_csv_format_multiple_vars(self):
        """CSV format with multiple variables."""
        result = format_match({'m': 36, 'n': 7}, 'csv')
        assert result == "m=36,n=7"

    def test_csv_format_empty(self):
        """CSV format with no variables."""
        result = format_match({}, 'csv')
        assert result == "found"


class TestFormatNoMatch:
    """Test no-match result formatting."""

    def test_text_format(self):
        """Text format for no match."""
        result = format_no_match('text')
        assert "No match" in result

    def test_json_format(self):
        """JSON format for no match."""
        result = format_no_match('json')
        parsed = json.loads(result)
        assert parsed['found'] is False
        assert parsed['variables'] is None

    def test_csv_format(self):
        """CSV format for no match."""
        result = format_no_match('csv')
        assert result == "not_found"


# =============================================================================
# Default Constants Tests
# =============================================================================

class TestDefaults:
    """Test default constants."""

    def test_defaults_singleton(self):
        """DEFAULTS singleton has expected values."""
        assert DEFAULTS.quantifier == "does_exist"
        assert DEFAULTS.lhs == "primesum(n,2)"
        assert DEFAULTS.operator == "=="
        assert DEFAULTS.rhs is None

    def test_default_bounds(self):
        """DEFAULT_BOUNDS has expected values."""
        assert DEFAULT_BOUNDS['n'] == 1000000
        assert DEFAULT_BOUNDS['m'] == 10000


# =============================================================================
# Issue #21: Equation Loading Tests
# =============================================================================

class TestParseVarString:
    """Test --var argument parsing."""

    def test_single_var(self):
        """Parse single variable assignment."""
        result = parse_var_string("a=3")
        assert result == {"a": "3"}

    def test_multiple_vars_comma(self):
        """Parse comma-separated variables."""
        result = parse_var_string("a=3,b=4")
        assert result == {"a": "3", "b": "4"}

    def test_with_spaces(self):
        """Handle spaces around comma."""
        result = parse_var_string("a=3, b=4")
        assert result == {"a": "3", "b": "4"}

    def test_float_value(self):
        """Parse float value."""
        result = parse_var_string("a=3.14")
        assert result == {"a": "3.14"}

    def test_type_hint_stripped(self):
        """Type hint is stripped from name."""
        result = parse_var_string("a:int=3")
        assert result == {"a": "3"}


class TestSavedEquation:
    """Test SavedEquation dataclass."""

    def test_to_components_basic(self):
        """Convert equation to components."""
        eq = SavedEquation(
            id="1",
            name="test",
            lhs="primesum(n,2)",
            operator="==",
            quantifier="does_exist",
        )
        components = eq.to_components()
        assert components.lhs == "primesum(n,2)"
        assert components.quantifier == "does_exist"

    def test_to_components_with_parameter_substitution(self):
        """Parameter substitution works."""
        eq = SavedEquation(
            id="1",
            name="test",
            lhs="primesum(n,a)",
            parameters={"a": ParameterDef(default=2)},
        )
        components = eq.to_components({"a": "3"})
        assert components.lhs == "primesum(n,3)"

    def test_to_components_uses_default_when_no_override(self):
        """Default parameter value used when no override."""
        eq = SavedEquation(
            id="1",
            name="test",
            lhs="primesum(n,a)",
            parameters={"a": ParameterDef(default=2)},
        )
        components = eq.to_components()
        assert components.lhs == "primesum(n,2)"


class TestEquationsFile:
    """Test EquationsFile loading and lookup."""

    def test_get_equation_by_id(self):
        """Look up equation by ID."""
        eq = SavedEquation(id="1", name="test", lhs="primesum(n,2)")
        ef = EquationsFile(version="1.0", equations={"1": eq})
        result = ef.get_equation("1")
        assert result is eq

    def test_get_equation_by_name(self):
        """Look up equation by name."""
        eq = SavedEquation(id="1", name="test-eq", lhs="primesum(n,2)")
        ef = EquationsFile(version="1.0", equations={"1": eq})
        result = ef.get_equation("test-eq")
        assert result is eq

    def test_get_equation_not_found(self):
        """Return None for unknown equation."""
        ef = EquationsFile(version="1.0", equations={})
        result = ef.get_equation("nonexistent")
        assert result is None

    def test_get_default(self):
        """Get default equation."""
        eq1 = SavedEquation(id="1", name="first", lhs="x", is_default=False)
        eq2 = SavedEquation(id="2", name="second", lhs="y", is_default=True)
        ef = EquationsFile(version="1.0", equations={"1": eq1, "2": eq2}, default_id="2")
        result = ef.get_default()
        assert result is eq2


class TestLoadEquationsFile:
    """Test loading equations.json from disk."""

    def test_load_valid_file(self):
        """Load valid equations.json."""
        # Use the actual equations.json in the project
        ef = load_equations_file()
        assert ef is not None
        assert ef.version == "1.0"
        assert len(ef.equations) >= 1

    def test_load_file_with_parameters(self):
        """Equations with parameters loaded correctly."""
        ef = load_equations_file()
        eq = ef.get_equation("1")
        assert eq is not None
        assert "a" in eq.parameters
        assert eq.parameters["a"].default == 2


class TestResolveDefaultEquation:
    """Test three-tier default resolution."""

    def test_config_takes_precedence(self):
        """config.json default_equation wins."""
        eq1 = SavedEquation(id="1", name="first", lhs="x", is_default=True)
        eq2 = SavedEquation(id="2", name="second", lhs="y", is_default=False)
        ef = EquationsFile(version="1.0", equations={"1": eq1, "2": eq2}, default_id="1")
        config = Config(default_equation="2")

        result, source = resolve_default_equation(ef, config)
        assert result is eq2
        assert source == "config"

    def test_equations_default_used_when_no_config(self):
        """equations.json default:true used when no config."""
        eq = SavedEquation(id="1", name="first", lhs="x", is_default=True)
        ef = EquationsFile(version="1.0", equations={"1": eq}, default_id="1")
        config = Config()

        result, source = resolve_default_equation(ef, config)
        assert result is eq
        assert source == "equations"

    def test_hardcoded_when_no_files(self):
        """Fall back to hardcoded when no equations."""
        config = Config()
        result, source = resolve_default_equation(None, config)
        assert result is None
        assert source == "hardcoded"


class TestResolveEffectiveDefaults:
    """Test dynamic default resolution for help text (Issue #63)."""

    def test_returns_expression_components(self):
        """Always returns an ExpressionComponents instance."""
        result = resolve_effective_defaults()
        assert isinstance(result, ExpressionComponents)
        assert len(result.lhs) > 0
        assert result.quantifier is not None
        assert result.operator is not None

    def test_stock_equations_resolves_correctly(self):
        """With stock equations.json, resolves to primesum(n,2) components."""
        # Stock equations.json has equation "1" as default with lhs="primesum(n,a)", a=2
        result = resolve_effective_defaults()
        assert result.lhs == "primesum(n,2)"
        assert result.quantifier == "does_exist"
        assert result.operator == "=="

    def test_fallback_when_no_files(self, tmp_path, monkeypatch):
        """Falls back to hardcoded defaults when no config files found."""
        monkeypatch.chdir(tmp_path)
        result = resolve_effective_defaults()
        assert result.lhs == DEFAULTS.lhs
        assert result.quantifier == DEFAULTS.quantifier
        assert result.operator == DEFAULTS.operator

    def test_handles_malformed_equations_gracefully(self, tmp_path, monkeypatch):
        """Malformed equations.json doesn't crash, returns hardcoded defaults."""
        monkeypatch.chdir(tmp_path)
        (tmp_path / "equations.json").write_text("{invalid json")
        result = resolve_effective_defaults()
        assert result.lhs == DEFAULTS.lhs

    def test_expr_and_lhs_stay_consistent(self):
        """The LHS in components matches what would appear in a full expression."""
        result = resolve_effective_defaults()
        # The LHS should appear in any expression built from these components
        result.rhs = "666"
        expr = result.to_expression()
        assert result.lhs in expr

    def test_quantifier_matches_equations_json(self):
        """Resolved quantifier comes from equations.json, not hardcoded."""
        # Load the actual equations.json default and verify it matches
        ef = load_equations_file()
        assert ef is not None
        default_eq = ef.get_default()
        assert default_eq is not None

        result = resolve_effective_defaults()
        assert result.quantifier == default_eq.quantifier

    def test_operator_matches_equations_json(self):
        """Resolved operator comes from equations.json, not hardcoded."""
        ef = load_equations_file()
        assert ef is not None
        default_eq = ef.get_default()
        assert default_eq is not None

        result = resolve_effective_defaults()
        assert result.operator == default_eq.operator

    def test_custom_equation_quantifier_propagates(self, tmp_path, monkeypatch):
        """Custom equations.json with for_any default propagates to resolved defaults."""
        monkeypatch.chdir(tmp_path)
        (tmp_path / "equations.json").write_text(json.dumps({
            "version": "1.0",
            "equations": {
                "1": {
                    "name": "custom",
                    "default": True,
                    "lhs": "tri(n)",
                    "operator": ">=",
                    "quantifier": "for_any"
                }
            }
        }))
        result = resolve_effective_defaults()
        assert result.quantifier == "for_any"
        assert result.operator == ">="
        assert result.lhs == "tri(n)"


class TestAlgorithmConfig:
    """Test algorithm configuration loading (Issue #29)."""

    def test_config_with_algorithm_settings(self, tmp_path):
        """Config loads algorithm settings correctly."""
        config_file = tmp_path / "config.json"
        config_file.write_text('''{
            "algorithms": {"sieve": "segmented"},
            "max_memory_mb": 512,
            "prefer": "minimal"
        }''')

        config = load_config(config_file)
        assert config.algorithms == {"sieve": "segmented"}
        assert config.max_memory_mb == 512
        assert config.prefer == "minimal"

    def test_config_without_algorithm_settings(self, tmp_path):
        """Config works without algorithm settings (defaults)."""
        config_file = tmp_path / "config.json"
        config_file.write_text('{"default_equation": "test"}')

        config = load_config(config_file)
        assert config.algorithms == {}
        assert config.max_memory_mb is None
        assert config.prefer is None

    def test_config_partial_algorithm_settings(self, tmp_path):
        """Config with only some algorithm settings."""
        config_file = tmp_path / "config.json"
        config_file.write_text('{"max_memory_mb": 256}')

        config = load_config(config_file)
        assert config.algorithms == {}
        assert config.max_memory_mb == 256
        assert config.prefer is None

    def test_config_multiple_algorithm_classes(self, tmp_path):
        """Config can specify multiple algorithm classes."""
        config_file = tmp_path / "config.json"
        config_file.write_text('''{
            "algorithms": {
                "sieve": "segmented",
                "fibonacci": "matrix"
            }
        }''')

        config = load_config(config_file)
        assert config.algorithms["sieve"] == "segmented"
        assert config.algorithms["fibonacci"] == "matrix"

    def test_empty_config_returns_defaults(self):
        """Empty/missing config returns default values."""
        config = Config()
        assert config.algorithms == {}
        assert config.max_memory_mb is None
        assert config.prefer is None


# =============================================================================
# Iterator Definition Tests (Issue #37)
# =============================================================================


class TestIteratorDef:
    """Tests for IteratorDef dataclass."""

    def test_defaults(self):
        """Check default values."""
        iter_def = IteratorDef()
        assert iter_def.type == "int"
        assert iter_def.dtype == "int"
        assert iter_def.start == 1
        assert iter_def.stop is None
        assert iter_def.step is None

    def test_max_alias(self):
        """Legacy 'max' field aliases to 'stop'."""
        iter_def = IteratorDef(max=100)
        assert iter_def.stop == 100

    def test_to_iterator_int(self):
        """to_iterator creates IntIterator."""
        iter_def = IteratorDef(type="int", start=1, stop=10, step=2)
        it = iter_def.to_iterator()
        result = list(it)
        assert result == [1, 3, 5, 7, 9]

    def test_to_iterator_int_with_dtype(self):
        """to_iterator respects dtype."""
        iter_def = IteratorDef(type="int", start=0, stop=5, dtype="uint64")
        it = iter_def.to_iterator()
        assert it.dtype == "uint64"
        result = list(it)
        assert result == [0, 1, 2, 3, 4, 5]

    def test_to_iterator_float(self):
        """to_iterator creates FloatIterator."""
        iter_def = IteratorDef(type="float", start=0.0, stop=0.5, step=0.1)
        it = iter_def.to_iterator()
        result = list(it)
        assert len(result) == 6
        assert result[0] == pytest.approx(0.0)
        assert result[-1] == pytest.approx(0.5)

    def test_to_iterator_float_num_steps(self):
        """to_iterator with num_steps creates linspace-style iterator."""
        iter_def = IteratorDef(type="float", start=0.0, stop=1.0, num_steps=11)
        it = iter_def.to_iterator()
        result = list(it)
        assert len(result) == 11
        assert result[5] == pytest.approx(0.5)


class TestParseIteratorDef:
    """Tests for parse_iterator_def function."""

    def test_basic_int(self):
        """Parse basic integer iterator."""
        var_name, iter_def = parse_iterator_def("n:1:1000")
        assert var_name == "n"
        assert iter_def.type == "int"
        assert iter_def.start == 1
        assert iter_def.stop == 1000
        assert iter_def.step is None

    def test_int_with_step(self):
        """Parse integer iterator with step."""
        var_name, iter_def = parse_iterator_def("n:1:100:2")
        assert var_name == "n"
        assert iter_def.start == 1
        assert iter_def.stop == 100
        assert iter_def.step == 2

    def test_int_with_dtype(self):
        """Parse integer iterator with dtype."""
        var_name, iter_def = parse_iterator_def("n:0:1000:1:uint64")
        assert var_name == "n"
        assert iter_def.dtype == "uint64"

    def test_float_auto_detect(self):
        """Auto-detect float from decimal values."""
        var_name, iter_def = parse_iterator_def("x:0.0:1.0")
        assert var_name == "x"
        assert iter_def.type == "float"
        assert iter_def.start == 0.0
        assert iter_def.stop == 1.0

    def test_float_with_step(self):
        """Parse float iterator with step."""
        var_name, iter_def = parse_iterator_def("x:0.0:1.0:0.1")
        assert var_name == "x"
        assert iter_def.step == 0.1

    def test_float_with_dtype(self):
        """Parse float iterator with dtype."""
        var_name, iter_def = parse_iterator_def("x:0.0:1.0::float32")
        assert var_name == "x"
        assert iter_def.dtype == "float32"

    def test_negative_values(self):
        """Parse with negative values."""
        var_name, iter_def = parse_iterator_def("n:-10:10:1")
        assert iter_def.start == -10
        assert iter_def.stop == 10

    def test_invalid_too_few_parts(self):
        """Raise on too few parts."""
        with pytest.raises(ValueError, match="Expected VAR:START:STOP"):
            parse_iterator_def("n:1")

    def test_invalid_empty_var(self):
        """Raise on empty variable name."""
        with pytest.raises(ValueError, match="Empty variable name"):
            parse_iterator_def(":1:100")

    def test_invalid_start(self):
        """Raise on invalid start value."""
        with pytest.raises(ValueError, match="Invalid start/stop"):
            parse_iterator_def("n:abc:100")

    def test_invalid_int_dtype(self):
        """Raise on invalid int dtype."""
        with pytest.raises(ValueError, match="Invalid dtype"):
            parse_iterator_def("n:1:100:1:float64")

    def test_invalid_float_dtype(self):
        """Raise on invalid float dtype."""
        with pytest.raises(ValueError, match="Invalid dtype"):
            parse_iterator_def("x:0.0:1.0:0.1:int32")


class TestBuildIteratorFactories:
    """Tests for build_iterator_factories_from_args function."""

    def test_from_bounds_only(self):
        """Create factories from bounds when no --var specified."""
        args = Namespace(iter_var=None, iter_type=None, iter_start=None,
                        iter_stop=None, iter_step=None, iter_num_steps=None,
                        iter_dtype=None)
        bounds = {'n': 100, 'm': 50}
        factories = build_iterator_factories_from_args(args, bounds)

        assert 'n' in factories
        assert 'm' in factories

        # Verify factory produces correct iterator
        it_n = factories['n']()
        assert list(it_n) == list(range(1, 101))

    def test_from_iter_var(self):
        """Create factories from --var syntax."""
        args = Namespace(iter_var=["n:1:10:2"], iter_type=None, iter_start=None,
                        iter_stop=None, iter_step=None, iter_num_steps=None,
                        iter_dtype=None)
        bounds = {}
        factories = build_iterator_factories_from_args(args, bounds)

        assert 'n' in factories
        it_n = factories['n']()
        assert list(it_n) == [1, 3, 5, 7, 9]

    def test_iter_var_overrides_bounds(self):
        """--var takes precedence over bounds."""
        args = Namespace(iter_var=["n:5:10:1"], iter_type=None, iter_start=None,
                        iter_stop=None, iter_step=None, iter_num_steps=None,
                        iter_dtype=None)
        bounds = {'n': 1000}  # Should be ignored
        factories = build_iterator_factories_from_args(args, bounds)

        it_n = factories['n']()
        assert list(it_n) == [5, 6, 7, 8, 9, 10]

    def test_multiple_iter_var(self):
        """Multiple --var specifications."""
        args = Namespace(iter_var=["n:1:5", "m:10:15"], iter_type=None,
                        iter_start=None, iter_stop=None, iter_step=None,
                        iter_num_steps=None, iter_dtype=None)
        bounds = {}
        factories = build_iterator_factories_from_args(args, bounds)

        assert 'n' in factories
        assert 'm' in factories

        it_n = factories['n']()
        it_m = factories['m']()
        assert list(it_n) == [1, 2, 3, 4, 5]
        assert list(it_m) == [10, 11, 12, 13, 14, 15]

    def test_iter_dtype_override(self):
        """--iter-dtype overrides default dtype."""
        args = Namespace(iter_var=["n:0:100"], iter_type=None, iter_start=None,
                        iter_stop=None, iter_step=None, iter_num_steps=None,
                        iter_dtype=["n:uint64"])
        bounds = {}
        factories = build_iterator_factories_from_args(args, bounds)

        it_n = factories['n']()
        assert it_n.dtype == "uint64"

    def test_float_iterator_factory(self):
        """Float iterator from --var."""
        args = Namespace(iter_var=["x:0.0:1.0:0.25"], iter_type=None,
                        iter_start=None, iter_stop=None, iter_step=None,
                        iter_num_steps=None, iter_dtype=None)
        bounds = {}
        factories = build_iterator_factories_from_args(args, bounds)

        it_x = factories['x']()
        result = list(it_x)
        assert len(result) == 5
        assert result[0] == pytest.approx(0.0)
        assert result[-1] == pytest.approx(1.0)
