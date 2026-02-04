"""
Tests for CLI utilities and expression building.

Issue: #18 (CLI rewrite)
Epic: #13 (Generalized Expression Grammar)
"""

import pytest
import json
from argparse import Namespace
from utils.cli import (
    ExpressionComponents,
    build_expression_from_args,
    build_bounds_from_args,
    format_match,
    format_no_match,
    DEFAULTS,
    DEFAULT_BOUNDS,
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

    def test_tier3_equation_raises_not_implemented(self):
        """--equation raises NotImplementedError (stub for #21)."""
        args = Namespace(
            expr=None,
            equation="1",
            lhs=None,
            rhs=None,
            operator=None,
            quantifier=None,
        )
        with pytest.raises(NotImplementedError, match="Issue #21"):
            build_expression_from_args(args)

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
        """Explicit --max-n overrides default."""
        args = Namespace(max_n=5000, max_m=None)
        bounds = build_bounds_from_args(args, "does_exist primesum(n,2) == 666")
        assert bounds['n'] == 5000
        assert bounds['m'] == DEFAULT_BOUNDS['m']

    def test_explicit_max_m(self):
        """Explicit --max-m overrides default."""
        args = Namespace(max_n=None, max_m=500)
        bounds = build_bounds_from_args(args, "does_exist primesum(n,2) == 666")
        assert bounds['n'] == DEFAULT_BOUNDS['n']
        assert bounds['m'] == 500

    def test_both_explicit(self):
        """Both bounds can be explicit."""
        args = Namespace(max_n=1000, max_m=100)
        bounds = build_bounds_from_args(args, "for_any primesum(n,2) == tri(m)")
        assert bounds['n'] == 1000
        assert bounds['m'] == 100


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
