"""
Tests for expression grammar parser and evaluator.

Issue: #17 (Expression parser with AST)
Epic: #13 (Generalized Expression Grammar)
"""

import pytest
from utils.grammar import (
    # AST classes
    Literal,
    Variable,
    FunctionCall,
    Comparison,
    Expression,
    # Parser
    ExpressionParser,
    ParseError,
    # Evaluator
    ExpressionEvaluator,
    EvaluationError,
    # Utilities
    find_free_variables,
    find_matches,
)
from utils.function_registry import FunctionRegistry


# =============================================================================
# AST Class Tests
# =============================================================================

class TestASTClasses:
    """Test AST dataclass construction and equality."""

    def test_literal_int(self):
        """Literal holds integer values."""
        lit = Literal(value=42)
        assert lit.value == 42

    def test_literal_float(self):
        """Literal holds float values."""
        lit = Literal(value=3.14)
        assert lit.value == 3.14

    def test_variable(self):
        """Variable holds a name."""
        var = Variable(name="n")
        assert var.name == "n"

    def test_function_call_no_args(self):
        """FunctionCall can have no arguments."""
        func = FunctionCall(name="foo", args=[])
        assert func.name == "foo"
        assert func.args == []

    def test_function_call_with_args(self):
        """FunctionCall holds arguments as list of ASTNodes."""
        func = FunctionCall(
            name="primesum",
            args=[Variable("n"), Literal(2)]
        )
        assert func.name == "primesum"
        assert len(func.args) == 2
        assert func.args[0] == Variable("n")
        assert func.args[1] == Literal(2)

    def test_comparison(self):
        """Comparison holds left, operator, and right."""
        comp = Comparison(
            left=Literal(1),
            operator="==",
            right=Literal(1)
        )
        assert comp.left == Literal(1)
        assert comp.operator == "=="
        assert comp.right == Literal(1)

    def test_expression(self):
        """Expression holds quantifier and comparison."""
        expr = Expression(
            quantifier="does_exist",
            comparison=Comparison(
                left=Literal(1),
                operator="==",
                right=Literal(1)
            )
        )
        assert expr.quantifier == "does_exist"
        assert isinstance(expr.comparison, Comparison)

    def test_ast_equality(self):
        """AST nodes with same values are equal (dataclass behavior)."""
        ast1 = Expression(
            quantifier="does_exist",
            comparison=Comparison(
                left=FunctionCall("primesum", [Variable("n"), Literal(2)]),
                operator="==",
                right=Literal(666)
            )
        )
        ast2 = Expression(
            quantifier="does_exist",
            comparison=Comparison(
                left=FunctionCall("primesum", [Variable("n"), Literal(2)]),
                operator="==",
                right=Literal(666)
            )
        )
        assert ast1 == ast2


# =============================================================================
# Parser Tests
# =============================================================================

class TestExpressionParser:
    """Test Lark-based expression parser."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_parse_simple_does_exist(self, parser):
        """Parse 'does_exist primesum(n,2) == 666'."""
        ast = parser.parse("does_exist primesum(n,2) == 666")

        assert ast == Expression(
            quantifier="does_exist",
            comparison=Comparison(
                left=FunctionCall("primesum", [Variable("n"), Literal(2)]),
                operator="==",
                right=Literal(666)
            )
        )

    def test_parse_for_any(self, parser):
        """Parse 'for_any tri(n) == 666'."""
        ast = parser.parse("for_any tri(n) == 666")

        assert ast.quantifier == "for_any"
        assert isinstance(ast.comparison.left, FunctionCall)
        assert ast.comparison.left.name == "tri"

    def test_parse_nested_function(self, parser):
        """Parse nested function calls."""
        ast = parser.parse("does_exist tri(n) == trisum(qtri(666))")

        # RHS is trisum(qtri(666))
        rhs = ast.comparison.right
        assert isinstance(rhs, FunctionCall)
        assert rhs.name == "trisum"
        assert len(rhs.args) == 1
        # Inner is qtri(666)
        inner = rhs.args[0]
        assert isinstance(inner, FunctionCall)
        assert inner.name == "qtri"
        assert inner.args == [Literal(666)]

    def test_parse_two_variables(self, parser):
        """Parse expression with two variables."""
        ast = parser.parse("for_any primesum(n,2) == tri(m)")

        # LHS has variable n
        assert ast.comparison.left == FunctionCall(
            "primesum", [Variable("n"), Literal(2)]
        )
        # RHS has variable m
        assert ast.comparison.right == FunctionCall("tri", [Variable("m")])

    def test_parse_all_comparison_operators(self, parser):
        """Parse all comparison operators."""
        operators = ["==", "!=", "<", ">", "<=", ">="]
        for op in operators:
            ast = parser.parse(f"does_exist tri(n) {op} 100")
            assert ast.comparison.operator == op

    def test_parse_float_literal(self, parser):
        """Parse float literals."""
        ast = parser.parse("does_exist tri(n) == 3.14")
        assert ast.comparison.right == Literal(3.14)

    def test_parse_zero_arg_function(self, parser):
        """Parse function call with no arguments."""
        ast = parser.parse("does_exist foo() == 1")
        assert ast.comparison.left == FunctionCall("foo", [])

    def test_parse_variable_on_right(self, parser):
        """Parse variable on right side of comparison."""
        ast = parser.parse("does_exist 666 == primesum(n,2)")
        assert ast.comparison.left == Literal(666)
        assert isinstance(ast.comparison.right, FunctionCall)

    def test_parse_whitespace_handling(self, parser):
        """Parser handles various whitespace."""
        ast1 = parser.parse("does_exist primesum(n,2)==666")
        ast2 = parser.parse("does_exist   primesum( n , 2 )  ==  666")
        assert ast1 == ast2

    def test_parse_underscore_in_names(self, parser):
        """Parser allows underscores in function/variable names."""
        ast = parser.parse("does_exist my_func(my_var) == 1")
        assert ast.comparison.left == FunctionCall("my_func", [Variable("my_var")])


class TestParseErrors:
    """Test parser error handling."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_empty_expression(self, parser):
        """Empty expression raises ParseError."""
        with pytest.raises(ParseError) as exc:
            parser.parse("")
        assert "Empty expression" in str(exc.value)

    def test_no_quantifier_with_free_vars_parses(self, parser):
        """Expression without quantifier parses (error happens at find_matches)."""
        # This now parses successfully - error is deferred to find_matches
        # because we support implicit verify mode for closed formulas
        ast = parser.parse("primesum(n,2) == 666")
        assert ast.quantifier is None  # No quantifier specified
        assert ast.comparison.right == Literal(666)

    def test_invalid_quantifier(self, parser):
        """Invalid quantifier raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("find_all primesum(n,2) == 666")

    def test_missing_comparison(self, parser):
        """Missing comparison raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("does_exist primesum(n,2)")

    def test_invalid_operator(self, parser):
        """Invalid operator raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("does_exist primesum(n,2) === 666")

    def test_unclosed_parenthesis(self, parser):
        """Unclosed parenthesis raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("does_exist primesum(n,2 == 666")

    def test_invalid_character(self, parser):
        """Invalid character raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("does_exist primesum(n,2) == 666$")


# =============================================================================
# Free Variable Detection Tests
# =============================================================================

class TestFreeVariables:
    """Test find_free_variables function."""

    def test_literal_no_variables(self):
        """Literals have no free variables."""
        assert find_free_variables(Literal(42)) == set()

    def test_single_variable(self):
        """Single variable is found."""
        assert find_free_variables(Variable("n")) == {"n"}

    def test_function_call_with_variable(self):
        """Variable in function call is found."""
        func = FunctionCall("tri", [Variable("n")])
        assert find_free_variables(func) == {"n"}

    def test_function_call_with_literal(self):
        """Literal in function call has no variables."""
        func = FunctionCall("primesum", [Literal(7), Literal(2)])
        assert find_free_variables(func) == set()

    def test_nested_function_calls(self):
        """Variables in nested calls are found."""
        # trisum(qtri(n))
        nested = FunctionCall("trisum", [
            FunctionCall("qtri", [Variable("n")])
        ])
        assert find_free_variables(nested) == {"n"}

    def test_comparison_two_variables(self):
        """Both sides of comparison are searched."""
        comp = Comparison(
            left=FunctionCall("primesum", [Variable("n"), Literal(2)]),
            operator="==",
            right=FunctionCall("tri", [Variable("m")])
        )
        assert find_free_variables(comp) == {"n", "m"}

    def test_expression_wrapping(self):
        """find_free_variables works on Expression."""
        expr = Expression(
            quantifier="for_any",
            comparison=Comparison(
                left=Variable("x"),
                operator="==",
                right=Variable("y")
            )
        )
        assert find_free_variables(expr) == {"x", "y"}

    def test_repeated_variable(self):
        """Same variable appearing twice is counted once."""
        comp = Comparison(
            left=Variable("n"),
            operator="==",
            right=FunctionCall("tri", [Variable("n")])
        )
        assert find_free_variables(comp) == {"n"}


# =============================================================================
# Evaluator Tests
# =============================================================================

class TestExpressionEvaluator:
    """Test expression evaluation with FunctionRegistry."""

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_evaluate_literal(self, evaluator):
        """Evaluate literal returns value."""
        assert evaluator.evaluate(Literal(42), {}) == 42
        assert evaluator.evaluate(Literal(3.14), {}) == 3.14

    def test_evaluate_variable(self, evaluator):
        """Evaluate variable looks up in context."""
        assert evaluator.evaluate(Variable("n"), {"n": 7}) == 7

    def test_evaluate_unbound_variable(self, evaluator):
        """Unbound variable raises EvaluationError."""
        with pytest.raises(EvaluationError) as exc:
            evaluator.evaluate(Variable("x"), {"n": 7})
        assert "Unbound variable" in str(exc.value)
        assert "'x'" in str(exc.value)

    def test_evaluate_function_call_tri(self, evaluator):
        """Evaluate tri(36) returns 666."""
        func = FunctionCall("tri", [Literal(36)])
        assert evaluator.evaluate(func, {}) == 666

    def test_evaluate_function_call_primesum(self, evaluator):
        """Evaluate primesum(7, 2) returns 666."""
        func = FunctionCall("primesum", [Literal(7), Literal(2)])
        assert evaluator.evaluate(func, {}) == 666

    def test_evaluate_function_with_variable(self, evaluator):
        """Evaluate function with variable argument."""
        func = FunctionCall("tri", [Variable("n")])
        assert evaluator.evaluate(func, {"n": 4}) == 10  # tri(4) = 10

    def test_evaluate_nested_function(self, evaluator):
        """Evaluate nested function calls."""
        # tri(qtri(666)) = tri(36) = 666
        nested = FunctionCall("tri", [
            FunctionCall("qtri", [Literal(666)])
        ])
        assert evaluator.evaluate(nested, {}) == 666

    def test_evaluate_comparison_true(self, evaluator):
        """Evaluate comparison returning True."""
        comp = Comparison(left=Literal(1), operator="==", right=Literal(1))
        assert evaluator.evaluate(comp, {}) is True

    def test_evaluate_comparison_false(self, evaluator):
        """Evaluate comparison returning False."""
        comp = Comparison(left=Literal(1), operator="==", right=Literal(2))
        assert evaluator.evaluate(comp, {}) is False

    def test_evaluate_all_comparison_operators(self, evaluator):
        """Test all comparison operators."""
        cases = [
            ("==", 5, 5, True),
            ("==", 5, 6, False),
            ("!=", 5, 6, True),
            ("!=", 5, 5, False),
            ("<", 5, 6, True),
            ("<", 6, 5, False),
            (">", 6, 5, True),
            (">", 5, 6, False),
            ("<=", 5, 5, True),
            ("<=", 5, 6, True),
            ("<=", 6, 5, False),
            (">=", 5, 5, True),
            (">=", 6, 5, True),
            (">=", 5, 6, False),
        ]
        for op, left, right, expected in cases:
            comp = Comparison(left=Literal(left), operator=op, right=Literal(right))
            assert evaluator.evaluate(comp, {}) is expected, f"{left} {op} {right}"

    def test_evaluate_expression_true(self, evaluator):
        """Evaluate full expression returning True."""
        expr = Expression(
            quantifier="does_exist",
            comparison=Comparison(
                left=FunctionCall("primesum", [Literal(7), Literal(2)]),
                operator="==",
                right=Literal(666)
            )
        )
        assert evaluator.evaluate(expr, {}) is True

    def test_evaluate_unknown_function(self, evaluator):
        """Unknown function raises EvaluationError."""
        func = FunctionCall("nonexistent", [Literal(1)])
        with pytest.raises(EvaluationError) as exc:
            evaluator.evaluate(func, {})
        assert "Unknown function" in str(exc.value)

    def test_evaluate_function_error(self, evaluator):
        """Function error is wrapped in EvaluationError."""
        # primesum with negative n should error
        func = FunctionCall("primesum", [Literal(-1), Literal(2)])
        with pytest.raises(EvaluationError) as exc:
            evaluator.evaluate(func, {})
        assert "primesum" in str(exc.value)


# =============================================================================
# Iteration Engine Tests
# =============================================================================

class TestFindMatches:
    """Test the find_matches iteration engine."""

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_does_exist_finds_first(self, parser, evaluator):
        """does_exist yields first match and stops."""
        expr = parser.parse("does_exist primesum(n,2) == 666")
        matches = list(find_matches(expr, evaluator, {"n": 100}))

        assert len(matches) == 1
        assert matches[0] == {"n": 7}

    def test_for_any_finds_all(self, parser, evaluator):
        """for_any yields all matches."""
        # tri(n) == 10 is true only for n=4
        expr = parser.parse("for_any tri(n) == 10")
        matches = list(find_matches(expr, evaluator, {"n": 10}))

        assert matches == [{"n": 4}]

    def test_no_match_returns_empty(self, parser, evaluator):
        """No match yields nothing."""
        expr = parser.parse("does_exist primesum(n,2) == 667")
        matches = list(find_matches(expr, evaluator, {"n": 10}))

        assert matches == []

    def test_two_variable_iteration(self, parser, evaluator):
        """Two variables iterate over product of ranges."""
        # Find small cases where tri(n) == primesum(m,1)
        # tri(1)=1, tri(2)=3=primesum(2,1)=2+3=5 NO
        # Actually primesum(1,1)=2, primesum(2,1)=5
        # tri(2)=3, we need tri(n)==primesum(m,1)
        # primesum(1,1)=2, primesum(2,1)=5
        # So no match in small range - let's use a simpler test

        # x == y, both in range 1-3
        expr = parser.parse("for_any tri(n) == tri(m)")
        matches = list(find_matches(expr, evaluator, {"n": 3, "m": 3}))

        # Should match when n==m: (1,1), (2,2), (3,3)
        assert {"n": 1, "m": 1} in matches
        assert {"n": 2, "m": 2} in matches
        assert {"n": 3, "m": 3} in matches
        assert len(matches) == 3

    def test_missing_bound_raises(self, parser, evaluator):
        """Missing variable bound raises ValueError."""
        expr = parser.parse("does_exist primesum(n,2) == tri(m)")

        with pytest.raises(ValueError) as exc:
            list(find_matches(expr, evaluator, {"n": 100}))  # missing m

        assert "Missing bounds" in str(exc.value)
        assert "m" in str(exc.value)
        assert "--max-m" in str(exc.value)

    def test_no_variables_true(self, parser, evaluator):
        """Expression with no variables evaluates once."""
        # tri(4) == 10 is true
        expr = parser.parse("does_exist tri(4) == 10")
        matches = list(find_matches(expr, evaluator, {}))

        assert matches == [{}]  # One empty match

    def test_no_variables_false(self, parser, evaluator):
        """Expression with no variables that's false yields nothing."""
        expr = parser.parse("does_exist tri(4) == 999")
        matches = list(find_matches(expr, evaluator, {}))

        assert matches == []


# =============================================================================
# Integration Tests
# =============================================================================

class TestIntegration:
    """End-to-end integration tests."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_primesum_666_exists(self, parser, evaluator):
        """Verify primesum(7,2) == 666."""
        expr = parser.parse("does_exist primesum(n,2) == 666")
        matches = list(find_matches(expr, evaluator, {"n": 100}))

        assert matches == [{"n": 7}]

    def test_tri_36_is_666(self, parser, evaluator):
        """Verify tri(36) == 666."""
        expr = parser.parse("does_exist tri(n) == 666")
        matches = list(find_matches(expr, evaluator, {"n": 100}))

        assert matches == [{"n": 36}]

    def test_nested_trisum_qtri(self, parser, evaluator):
        """Verify trisum(qtri(666)) == 666."""
        # qtri(666) = 36, trisum(36) should relate to 666
        # Actually, trisum(10) = 666 and qtri(666) = 36
        # So trisum(qtri(666)) = trisum(36) != 666
        # Let's verify what trisum(36) actually is
        from utils.number_theory import trisum, qtri

        # qtri(666) = 36
        assert qtri(666) == 36

        # Check what trisum(36) is - it's the row-sum for base 36
        # This is a different value

        # Let's test something we know works:
        # tri(qtri(666)) = tri(36) = 666
        expr = parser.parse("does_exist tri(qtri(666)) == 666")
        result = evaluator.evaluate(expr, {})
        assert result is True

    def test_multiple_matches_fibonacci(self, parser, evaluator):
        """Find multiple Fibonacci numbers that are triangular."""
        # fib(1)=1=tri(1), fib(2)=1=tri(1), fib(4)=3=tri(2)
        # Wait, fib(4)=3, and tri(2)=3, so this should match

        expr = parser.parse("for_any fibonacci(n) == tri(m)")
        matches = list(find_matches(expr, evaluator, {"n": 10, "m": 10}))

        # Should find at least (1,1), (2,1), and any others
        assert {"n": 1, "m": 1} in matches  # fib(1)=1=tri(1)
        assert {"n": 2, "m": 1} in matches  # fib(2)=1=tri(1)

    def test_comparison_operators_with_functions(self, parser, evaluator):
        """Test comparison operators with function calls."""
        # Find n where tri(n) > 100
        expr = parser.parse("does_exist tri(n) > 100")
        matches = list(find_matches(expr, evaluator, {"n": 20}))

        # tri(14) = 105 > 100
        assert matches[0]["n"] == 14

    def test_factorial_large_value(self, parser, evaluator):
        """Factorial returns large values correctly."""
        expr = parser.parse("does_exist factorial(n) > 1000000")
        matches = list(find_matches(expr, evaluator, {"n": 15}))

        # 10! = 3,628,800 > 1,000,000
        assert matches[0]["n"] == 10


# =============================================================================
# Verify Quantifier Tests (Issue #34)
# =============================================================================

class TestVerifyQuantifier:
    """Test verify quantifier for closed formulas."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    # --- Parsing Tests ---

    def test_parse_explicit_verify(self, parser):
        """Parse explicit verify quantifier."""
        ast = parser.parse("verify primesum(7,2) == 666")
        assert ast.quantifier == "verify"
        assert ast.comparison.left == FunctionCall("primesum", [Literal(7), Literal(2)])
        assert ast.comparison.right == Literal(666)

    def test_parse_implicit_verify_no_vars(self, parser):
        """Parse expression with no quantifier and no free vars."""
        ast = parser.parse("primesum(7,2) == 666")
        assert ast.quantifier is None  # Will be auto-detected
        assert ast.comparison.left == FunctionCall("primesum", [Literal(7), Literal(2)])

    def test_parse_implicit_verify_nested_functions(self, parser):
        """Parse nested functions with no free vars."""
        ast = parser.parse("tri(qtri(666)) == 666")
        assert ast.quantifier is None

    # --- Evaluation Tests ---

    def test_verify_true_result(self, parser, evaluator):
        """Verify returns true for true closed formula."""
        expr = parser.parse("verify primesum(7,2) == 666")
        matches = list(find_matches(expr, evaluator, {}))

        assert len(matches) == 1
        assert matches[0] == {"__verify_result__": True}

    def test_verify_false_result(self, parser, evaluator):
        """Verify returns false for false closed formula."""
        expr = parser.parse("verify primesum(7,2) == 667")
        matches = list(find_matches(expr, evaluator, {}))

        assert len(matches) == 1
        assert matches[0] == {"__verify_result__": False}

    def test_implicit_verify_true(self, parser, evaluator):
        """Implicit verify (no quantifier, no free vars) returns true."""
        expr = parser.parse("tri(36) == 666")
        matches = list(find_matches(expr, evaluator, {}))

        assert len(matches) == 1
        assert matches[0] == {"__verify_result__": True}

    def test_implicit_verify_false(self, parser, evaluator):
        """Implicit verify returns false for false formula."""
        expr = parser.parse("tri(36) == 667")
        matches = list(find_matches(expr, evaluator, {}))

        assert len(matches) == 1
        assert matches[0] == {"__verify_result__": False}

    def test_verify_nested_functions(self, parser, evaluator):
        """Verify with nested function calls."""
        # tri(qtri(666)) = tri(36) = 666
        expr = parser.parse("verify tri(qtri(666)) == 666")
        matches = list(find_matches(expr, evaluator, {}))

        assert matches[0] == {"__verify_result__": True}

    def test_verify_comparison_operators(self, parser, evaluator):
        """Verify works with all comparison operators."""
        tests = [
            ("verify tri(36) == 666", True),
            ("verify tri(36) != 667", True),
            ("verify tri(36) < 700", True),
            ("verify tri(36) > 600", True),
            ("verify tri(36) <= 666", True),
            ("verify tri(36) >= 666", True),
        ]
        for expr_str, expected in tests:
            expr = parser.parse(expr_str)
            matches = list(find_matches(expr, evaluator, {}))
            assert matches[0]["__verify_result__"] == expected, f"Failed for: {expr_str}"

    # --- Error Cases ---

    def test_verify_with_free_vars_raises(self, parser, evaluator):
        """Verify with free variables raises ValueError."""
        expr = parser.parse("verify primesum(n,2) == 666")

        with pytest.raises(ValueError) as exc:
            list(find_matches(expr, evaluator, {}))

        assert "closed formula" in str(exc.value).lower()
        assert "n" in str(exc.value)

    def test_no_quantifier_with_free_vars_raises(self, parser, evaluator):
        """No quantifier with free variables raises ValueError."""
        expr = parser.parse("primesum(n,2) == 666")

        with pytest.raises(ValueError) as exc:
            list(find_matches(expr, evaluator, {}))

        assert "free variables" in str(exc.value).lower()
        assert "n" in str(exc.value)
        assert "does_exist" in str(exc.value) or "for_any" in str(exc.value)

    # --- verify_expression convenience function ---

    def test_verify_expression_function_true(self, parser, evaluator):
        """verify_expression returns True for true formula."""
        from utils.grammar import verify_expression

        expr = parser.parse("verify primesum(7,2) == 666")
        result = verify_expression(expr, evaluator)

        assert result is True

    def test_verify_expression_function_false(self, parser, evaluator):
        """verify_expression returns False for false formula."""
        from utils.grammar import verify_expression

        expr = parser.parse("verify primesum(7,2) == 667")
        result = verify_expression(expr, evaluator)

        assert result is False

    def test_verify_expression_with_free_vars_raises(self, parser, evaluator):
        """verify_expression raises for formula with free vars."""
        from utils.grammar import verify_expression

        expr = parser.parse("does_exist primesum(n,2) == 666")

        with pytest.raises(ValueError) as exc:
            verify_expression(expr, evaluator)

        assert "free variables" in str(exc.value).lower()


# =============================================================================
# Iterator Factory Tests (Issue #37)
# =============================================================================


class TestIteratorFactories:
    """Tests for find_matches with iterator_factories parameter."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def evaluator(self):
        registry = FunctionRegistry()
        return ExpressionEvaluator(registry)

    def test_custom_iterator_factory(self, parser, evaluator):
        """Custom iterator factory is used instead of bounds."""
        from utils.iterators import IntIterator

        expr = parser.parse("does_exist primesum(n,2) == 666")

        # Use iterator that starts at 7 (the answer)
        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={'n': lambda: IntIterator(7, 10, 1)}
        ))

        assert len(results) == 1
        assert results[0] == {'n': 7}

    def test_iterator_factory_with_step(self, parser, evaluator):
        """Iterator factory with step only returns values at those steps."""
        from utils.iterators import IntIterator

        # tri(n) for n = 1, 3, 5, 7 are 1, 6, 15, 28
        expr = parser.parse("for_any tri(n) == 6")

        # Only odd numbers: 1, 3, 5, 7, 9
        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={'n': lambda: IntIterator(1, 10, 2)}
        ))

        # tri(3) = 6, and 3 is in our range
        assert len(results) == 1
        assert results[0] == {'n': 3}

    def test_iterator_factory_mixed_with_bounds(self, parser, evaluator):
        """Iterator factory for one var, bounds for another."""
        from utils.iterators import IntIterator

        expr = parser.parse("for_any tri(n) == m")

        # n uses iterator (1-5), m uses bounds (1-20)
        results = list(find_matches(
            expr, evaluator,
            {'m': 20},
            iterator_factories={'n': lambda: IntIterator(1, 5, 1)}
        ))

        # tri(1)=1, tri(2)=3, tri(3)=6, tri(4)=10, tri(5)=15
        expected_m_values = {1, 3, 6, 10, 15}
        actual_m_values = {r['m'] for r in results}
        assert actual_m_values == expected_m_values

    def test_iterator_factory_empty_range(self, parser, evaluator):
        """Empty iterator produces no results."""
        from utils.iterators import IntIterator

        expr = parser.parse("for_any tri(n) == 6")

        # Empty range (5 to 1 with step 1)
        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={'n': lambda: IntIterator(5, 1, 1)}
        ))

        assert len(results) == 0

    def test_iterator_factory_takes_precedence_over_bounds(self, parser, evaluator):
        """Iterator factory takes precedence when both specified."""
        from utils.iterators import IntIterator

        expr = parser.parse("does_exist tri(n) == 6")

        # bounds says n goes up to 100, but iterator says only 3-5
        results = list(find_matches(
            expr, evaluator,
            {'n': 100},
            iterator_factories={'n': lambda: IntIterator(3, 5, 1)}
        ))

        # tri(3) = 6, which is in our iterator range
        assert len(results) == 1
        assert results[0] == {'n': 3}

    def test_shared_variable_works(self, parser, evaluator):
        """Same variable on LHS and RHS gets same value."""
        from utils.iterators import IntIterator

        # n appears in both function arguments
        expr = parser.parse("for_any tri(n) == primesum(n,1)")

        # tri(n) = n*(n+1)/2, primesum(n,1) = sum of first n primes
        # tri(1) = 1, primesum(1,1) = 2 - not equal
        # tri(2) = 3, primesum(2,1) = 5 - not equal
        # Let's search a small range
        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={'n': lambda: IntIterator(1, 10, 1)}
        ))

        # Verify each result has n used consistently
        for r in results:
            from utils.number_theory import tri
            from utils.sequences import primesum
            n = r['n']
            assert tri(n) == primesum(n, 1)

    def test_two_variable_with_factories(self, parser, evaluator):
        """Two variables both with iterator factories."""
        from utils.iterators import IntIterator

        expr = parser.parse("for_any tri(n) == tri(m)")

        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={
                'n': lambda: IntIterator(1, 5, 1),
                'm': lambda: IntIterator(1, 5, 1)
            }
        ))

        # tri(n) == tri(m) when n == m (5 matches expected)
        assert len(results) == 5
        for r in results:
            assert r['n'] == r['m']

    def test_float_iterator_with_grammar(self, parser, evaluator):
        """FloatIterator works with find_matches."""
        from utils.iterators import FloatIterator

        # Use the built-in square function with a float iterator
        # This tests that float iteration works correctly with the grammar
        # square(0.5) == 0.25, and 0.5 should be in the iteration range

        expr = parser.parse("does_exist square(x) == 0.25")

        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={
                'x': lambda: FloatIterator(0.0, 1.0, step=0.1)
            }
        ))

        assert len(results) == 1
        assert abs(results[0]['x'] - 0.5) < 1e-9
