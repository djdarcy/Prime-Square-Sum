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
    ContextBlock,
    Expression,
    BinaryOp,
    UnaryOp,
    # Parser
    ExpressionParser,
    ParseError,
    # Evaluator
    ExpressionEvaluator,
    EvaluationError,
    # Utilities
    find_free_variables,
    find_matches,
    validate_expression,
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
            operands=[Literal(1), Literal(1)],
            operators=["=="]
        )
        assert comp.operands[0] == Literal(1)
        assert comp.operators[0] == "=="
        assert comp.operands[1] == Literal(1)

    def test_expression(self):
        """Expression holds quantifier and comparison."""
        expr = Expression(
            quantifier="does_exist",
            body=Comparison(
                operands=[Literal(1), Literal(1)],
                operators=["=="]
            )
        )
        assert expr.quantifier == "does_exist"
        assert isinstance(expr.body, Comparison)

    def test_ast_equality(self):
        """AST nodes with same values are equal (dataclass behavior)."""
        ast1 = Expression(
            quantifier="does_exist",
            body=Comparison(
                operands=[FunctionCall("primesum", [Variable("n"), Literal(2)]), Literal(666)],
                operators=["=="]
            )
        )
        ast2 = Expression(
            quantifier="does_exist",
            body=Comparison(
                operands=[FunctionCall("primesum", [Variable("n"), Literal(2)]), Literal(666)],
                operators=["=="]
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
            body=Comparison(
                operands=[FunctionCall("primesum", [Variable("n"), Literal(2)]), Literal(666)],
                operators=["=="]
            )
        )

    def test_parse_for_any(self, parser):
        """Parse 'for_any tri(n) == 666'."""
        ast = parser.parse("for_any tri(n) == 666")

        assert ast.quantifier == "for_any"
        assert isinstance(ast.body.operands[0], FunctionCall)
        assert ast.body.operands[0].name == "tri"

    def test_parse_nested_function(self, parser):
        """Parse nested function calls."""
        ast = parser.parse("does_exist tri(n) == trisum(qtri(666))")

        # RHS is trisum(qtri(666))
        rhs = ast.body.operands[1]
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
        assert ast.body.operands[0] == FunctionCall(
            "primesum", [Variable("n"), Literal(2)]
        )
        # RHS has variable m
        assert ast.body.operands[1] == FunctionCall("tri", [Variable("m")])

    def test_parse_all_comparison_operators(self, parser):
        """Parse all comparison operators."""
        operators = ["==", "!=", "<", ">", "<=", ">="]
        for op in operators:
            ast = parser.parse(f"does_exist tri(n) {op} 100")
            assert ast.body.operators[0] == op

    def test_parse_float_literal(self, parser):
        """Parse float literals."""
        ast = parser.parse("does_exist tri(n) == 3.14")
        assert ast.body.operands[1] == Literal(3.14)

    def test_parse_zero_arg_function(self, parser):
        """Parse function call with no arguments."""
        ast = parser.parse("does_exist foo() == 1")
        assert ast.body.operands[0] == FunctionCall("foo", [])

    def test_parse_variable_on_right(self, parser):
        """Parse variable on right side of comparison."""
        ast = parser.parse("does_exist 666 == primesum(n,2)")
        assert ast.body.operands[0] == Literal(666)
        assert isinstance(ast.body.operands[1], FunctionCall)

    def test_parse_whitespace_handling(self, parser):
        """Parser handles various whitespace."""
        ast1 = parser.parse("does_exist primesum(n,2)==666")
        ast2 = parser.parse("does_exist   primesum( n , 2 )  ==  666")
        assert ast1 == ast2

    def test_parse_underscore_in_names(self, parser):
        """Parser allows underscores in function/variable names."""
        ast = parser.parse("does_exist my_func(my_var) == 1")
        assert ast.body.operands[0] == FunctionCall("my_func", [Variable("my_var")])


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
        assert ast.body.operands[1] == Literal(666)

    def test_invalid_quantifier(self, parser):
        """Invalid quantifier raises ParseError."""
        with pytest.raises(ParseError):
            parser.parse("find_all primesum(n,2) == 666")

    def test_bare_expression_is_valid(self, parser):
        """Expression without comparison is valid (body can be any expression).

        With Phase 3 grammar, a bare function call like 'primesum(n,2)' is
        parseable — it evaluates to the function's return value.
        """
        ast = parser.parse("does_exist primesum(n,2)")
        assert ast.quantifier == "does_exist"
        assert isinstance(ast.body, FunctionCall)

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
            operands=[FunctionCall("primesum", [Variable("n"), Literal(2)]), FunctionCall("tri", [Variable("m")])],
            operators=["=="]
        )
        assert find_free_variables(comp) == {"n", "m"}

    def test_expression_wrapping(self):
        """find_free_variables works on Expression."""
        expr = Expression(
            quantifier="for_any",
            body=Comparison(
                operands=[Variable("x"), Variable("y")],
                operators=["=="]
            )
        )
        assert find_free_variables(expr) == {"x", "y"}

    def test_repeated_variable(self):
        """Same variable appearing twice is counted once."""
        comp = Comparison(
            operands=[Variable("n"), FunctionCall("tri", [Variable("n")])],
            operators=["=="]
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
        comp = Comparison(operands=[Literal(1), Literal(1)], operators=["=="])
        assert evaluator.evaluate(comp, {}) is True

    def test_evaluate_comparison_false(self, evaluator):
        """Evaluate comparison returning False."""
        comp = Comparison(operands=[Literal(1), Literal(2)], operators=["=="])
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
            comp = Comparison(operands=[Literal(left), Literal(right)], operators=[op])
            assert evaluator.evaluate(comp, {}) is expected, f"{left} {op} {right}"

    def test_evaluate_expression_true(self, evaluator):
        """Evaluate full expression returning True."""
        expr = Expression(
            quantifier="does_exist",
            body=Comparison(
                operands=[FunctionCall("primesum", [Literal(7), Literal(2)]), Literal(666)],
                operators=["=="]
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
        assert ast.body.operands[0] == FunctionCall("primesum", [Literal(7), Literal(2)])
        assert ast.body.operands[1] == Literal(666)

    def test_parse_implicit_verify_no_vars(self, parser):
        """Parse expression with no quantifier and no free vars."""
        ast = parser.parse("primesum(7,2) == 666")
        assert ast.quantifier is None  # Will be auto-detected
        assert ast.body.operands[0] == FunctionCall("primesum", [Literal(7), Literal(2)])

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

    def test_implicit_does_exist_with_comparison(self, parser, evaluator):
        """No quantifier + free vars + comparison → implicit does_exist."""
        expr = parser.parse("tri(n) == 666")
        matches = list(find_matches(expr, evaluator, {'n': 100}))

        assert len(matches) == 1
        assert matches[0]['n'] == 36

    def test_implicit_for_any_bare_term(self, parser, evaluator):
        """No quantifier + free vars + no comparison → implicit for_any."""
        expr = parser.parse("tri(n)")
        matches = list(find_matches(expr, evaluator, {'n': 5}))

        assert len(matches) == 5
        assert matches[0] == {'n': 1, '__value__': 1}
        assert matches[1] == {'n': 2, '__value__': 3}
        assert matches[2] == {'n': 3, '__value__': 6}
        assert matches[3] == {'n': 4, '__value__': 10}
        assert matches[4] == {'n': 5, '__value__': 15}

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

        # Use the built-in pow function with a float iterator
        # pow(0.5, 2) == 0.25, and 0.5 should be in the iteration range
        expr = parser.parse("does_exist pow(x, 2) == 0.25")

        results = list(find_matches(
            expr, evaluator, {},
            iterator_factories={
                'x': lambda: FloatIterator(0.0, 1.0, step=0.1)
            }
        ))

        assert len(results) == 1
        assert abs(results[0]['x'] - 0.5) < 1e-9


# =============================================================================
# Dotted Names / Namespace Grammar Tests (Issue #46)
# =============================================================================

class TestDottedNames:
    """Tests for dotted function names in grammar (Issue #46)."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_parse_math_namespace(self, parser):
        """Parse math.pow(n, 2) == 25."""
        ast = parser.parse("does_exist math.pow(n, 2) == 25")
        assert ast.body.operands[0] == FunctionCall("math.pow", [Variable("n"), Literal(2)])

    def test_parse_pss_namespace(self, parser):
        """Parse pss.tri(n) == 666."""
        ast = parser.parse("does_exist pss.tri(n) == 666")
        assert ast.body.operands[0] == FunctionCall("pss.tri", [Variable("n")])

    def test_parse_user_namespace(self, parser):
        """Parse user.custom(n) == 42."""
        ast = parser.parse("does_exist user.custom(n) == 42")
        assert ast.body.operands[0] == FunctionCall("user.custom", [Variable("n")])

    def test_parse_unqualified_still_works(self, parser):
        """Unqualified names still parse correctly."""
        ast = parser.parse("does_exist primesum(n, 2) == 666")
        assert ast.body.operands[0] == FunctionCall("primesum", [Variable("n"), Literal(2)])

    def test_parse_mixed_qualified_unqualified(self, parser):
        """Mix of qualified and unqualified in same expression."""
        ast = parser.parse("does_exist math.pow(n, 2) == pss.tri(m)")
        assert ast.body.operands[0] == FunctionCall("math.pow", [Variable("n"), Literal(2)])
        assert ast.body.operands[1] == FunctionCall("pss.tri", [Variable("m")])

    def test_parse_float_not_confused(self, parser):
        """Float literal 2.5 is not confused with a dotted name."""
        ast = parser.parse("does_exist math.pow(n, 2.5) == 100")
        assert ast.body.operands[0].args[1] == Literal(2.5)
        assert ast.body.operands[0].name == "math.pow"

    def test_parse_nested_dotted(self, parser):
        """Nested dotted function calls."""
        ast = parser.parse("does_exist pss.tri(pss.qtri(666)) == 666")
        outer = ast.body.operands[0]
        assert outer.name == "pss.tri"
        inner = outer.args[0]
        assert inner.name == "pss.qtri"
        assert inner.args == [Literal(666)]


class TestDottedNameIntegration:
    """Integration tests for namespaced function evaluation (Issue #46)."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def evaluator(self):
        from utils.function_registry import FunctionRegistry
        return ExpressionEvaluator(FunctionRegistry())

    def test_qualified_math_evaluates(self, parser, evaluator):
        """Qualified math function call evaluates correctly."""
        expr = parser.parse("verify math.pow(2, 10) == 1024")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0] == {"__verify_result__": True}

    def test_qualified_pss_evaluates(self, parser, evaluator):
        """Qualified PSS function call evaluates correctly."""
        expr = parser.parse("verify pss.tri(36) == 666")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0] == {"__verify_result__": True}

    def test_qualified_trig_evaluates(self, parser, evaluator):
        """Auto-registered trig function evaluates in expression."""
        expr = parser.parse("verify math.floor(math.sin(0)) == 0")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0] == {"__verify_result__": True}

    def test_nested_qualified_evaluates(self, parser, evaluator):
        """Nested qualified calls evaluate correctly."""
        expr = parser.parse("verify pss.tri(pss.qtri(666)) == 666")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0] == {"__verify_result__": True}

    def test_mixed_namespaces_search(self, parser, evaluator):
        """Search with mixed namespaces finds results."""
        expr = parser.parse("does_exist math.pow(n, 2) == pss.tri(m)")
        matches = list(find_matches(expr, evaluator, {"n": 10, "m": 10}))
        # Verify any match found is correct
        for match in matches:
            n, m = match['n'], match['m']
            assert n ** 2 == m * (m + 1) // 2


# =============================================================================
# Arithmetic Operator AST Tests (Phase 2, Issue #44)
# =============================================================================

class TestArithmeticAST:
    """Test BinaryOp and UnaryOp AST dataclass construction."""

    def test_binary_op_construction(self):
        node = BinaryOp(left=Literal(2), operator='+', right=Literal(3))
        assert node.left == Literal(2)
        assert node.operator == '+'
        assert node.right == Literal(3)

    def test_unary_op_construction(self):
        node = UnaryOp(operator='-', operand=Literal(5))
        assert node.operator == '-'
        assert node.operand == Literal(5)

    def test_binary_op_equality(self):
        a = BinaryOp(Literal(1), '+', Literal(2))
        b = BinaryOp(Literal(1), '+', Literal(2))
        assert a == b

    def test_nested_binary_ops(self):
        """BinaryOp can nest: (1 + 2) * 3."""
        inner = BinaryOp(Literal(1), '+', Literal(2))
        outer = BinaryOp(inner, '*', Literal(3))
        assert outer.left == inner
        assert outer.operator == '*'


# =============================================================================
# Arithmetic Parsing Tests
# =============================================================================

class TestArithmeticParsing:
    """Test that arithmetic expressions parse into correct AST structures."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    # --- Basic operators ---

    def test_parse_addition(self, parser):
        expr = parser.parse("verify 2 + 3 == 5")
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '+'
        assert left.left == Literal(2)
        assert left.right == Literal(3)

    def test_parse_subtraction(self, parser):
        expr = parser.parse("verify 10 - 4 == 6")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '-'

    def test_parse_multiplication(self, parser):
        expr = parser.parse("verify 3 * 7 == 21")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '*'

    def test_parse_division(self, parser):
        expr = parser.parse("verify 7 / 2 == 3.5")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '/'

    def test_parse_floor_division(self, parser):
        expr = parser.parse("verify 7 // 2 == 3")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '//'

    def test_parse_modulo(self, parser):
        expr = parser.parse("verify 7 % 3 == 1")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '%'

    def test_parse_exponentiation(self, parser):
        expr = parser.parse("verify 2 ** 10 == 1024")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert expr.body.operands[0].operator == '**'

    # --- Unary operators ---

    def test_parse_unary_minus(self, parser):
        expr = parser.parse("verify -5 == -5")
        left = expr.body.operands[0]
        assert isinstance(left, UnaryOp)
        assert left.operator == '-'
        assert left.operand == Literal(5)

    def test_parse_unary_plus(self, parser):
        expr = parser.parse("verify +5 == 5")
        left = expr.body.operands[0]
        assert isinstance(left, UnaryOp)
        assert left.operator == '+'

    def test_parse_double_negative(self, parser):
        """--3 parses as neg(neg(3))."""
        expr = parser.parse("verify --3 == 3")
        left = expr.body.operands[0]
        assert isinstance(left, UnaryOp)
        assert isinstance(left.operand, UnaryOp)
        assert left.operand.operand == Literal(3)

    # --- Precedence ---

    def test_precedence_mul_over_add(self, parser):
        """2 + 3 * 4 should parse as 2 + (3 * 4), not (2 + 3) * 4."""
        expr = parser.parse("verify 2 + 3 * 4 == 14")
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '+'
        assert left.left == Literal(2)
        assert isinstance(left.right, BinaryOp)
        assert left.right.operator == '*'

    def test_precedence_parens_override(self, parser):
        """(2 + 3) * 4 should parse as mul(add(2,3), 4)."""
        expr = parser.parse("verify (2 + 3) * 4 == 20")
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '*'
        assert isinstance(left.left, BinaryOp)
        assert left.left.operator == '+'

    def test_precedence_power_over_mul(self, parser):
        """2 * 3 ** 2 should parse as 2 * (3 ** 2)."""
        expr = parser.parse("verify 2 * 3 ** 2 == 18")
        left = expr.body.operands[0]
        assert left.operator == '*'
        assert isinstance(left.right, BinaryOp)
        assert left.right.operator == '**'

    def test_precedence_unary_minus_and_power(self, parser):
        """-3**2 should parse as -(3**2), not (-3)**2. Python convention."""
        expr = parser.parse("verify -3**2 == -9")
        left = expr.body.operands[0]
        assert isinstance(left, UnaryOp)
        assert left.operator == '-'
        assert isinstance(left.operand, BinaryOp)
        assert left.operand.operator == '**'

    # --- Associativity ---

    def test_right_associativity_power(self, parser):
        """2**3**2 should parse as 2**(3**2), not (2**3)**2."""
        expr = parser.parse("verify 2**3**2 == 512")
        left = expr.body.operands[0]
        assert left.operator == '**'
        assert left.left == Literal(2)
        assert isinstance(left.right, BinaryOp)
        assert left.right.operator == '**'
        assert left.right.left == Literal(3)

    def test_left_associativity_subtraction(self, parser):
        """10 - 3 - 2 should parse as (10 - 3) - 2."""
        expr = parser.parse("verify 10 - 3 - 2 == 5")
        left = expr.body.operands[0]
        assert left.operator == '-'
        assert isinstance(left.left, BinaryOp)
        assert left.left.operator == '-'

    # --- Parenthesized expressions ---

    def test_nested_parens(self, parser):
        expr = parser.parse("verify ((2 + 3)) == 5")
        # Should still evaluate correctly
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '+'

    # --- Mixed with functions ---

    def test_arithmetic_with_function(self, parser):
        """tri(4) + 1 should parse as add(FunctionCall, Literal)."""
        expr = parser.parse("verify tri(4) + 1 == 11")
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '+'
        assert isinstance(left.left, FunctionCall)
        assert left.left.name == 'tri'

    def test_arithmetic_in_function_args(self, parser):
        """Functions can take arithmetic expressions as arguments."""
        expr = parser.parse("verify pow(2 + 1, 2) == 9")
        left = expr.body.operands[0]
        assert isinstance(left, FunctionCall)
        assert isinstance(left.args[0], BinaryOp)
        assert left.args[0].operator == '+'

    def test_arithmetic_both_sides(self, parser):
        """Arithmetic on both sides of comparison."""
        expr = parser.parse("verify 2 + 3 == 10 - 5")
        assert isinstance(expr.body.operands[0], BinaryOp)
        assert isinstance(expr.body.operands[1], BinaryOp)

    def test_power_unary_right(self, parser):
        """2**-3 should parse as power(2, neg(3))."""
        expr = parser.parse("verify 2**-3 == 0.125")
        left = expr.body.operands[0]
        assert isinstance(left, BinaryOp)
        assert left.operator == '**'
        assert isinstance(left.right, UnaryOp)
        assert left.right.operator == '-'


# =============================================================================
# Arithmetic Evaluation Tests
# =============================================================================

class TestArithmeticEvaluation:
    """Test arithmetic expression evaluation produces correct results."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def _verify(self, parser, evaluator, expr_str):
        """Helper: parse and evaluate a verify expression, return comparison result."""
        ast = parser.parse(expr_str)
        return evaluator.evaluate(ast.body, {})

    # --- Basic operations ---

    def test_addition(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 + 3 == 5")

    def test_subtraction(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 10 - 4 == 6")

    def test_multiplication(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 3 * 7 == 21")

    def test_true_division(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 7 / 2 == 3.5")

    def test_floor_division(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 7 // 2 == 3")

    def test_negative_floor_division(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify -7 // 2 == -4")

    def test_modulo(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 7 % 3 == 1")

    def test_exponentiation(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 ** 10 == 1024")

    def test_unary_minus(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify -5 + 8 == 3")

    def test_double_negation(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify -(-3) == 3")

    # --- Precedence evaluation ---

    def test_precedence_add_mul(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 + 3 * 4 == 14")

    def test_precedence_parens(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify (2 + 3) * 4 == 20")

    def test_precedence_power_mul(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 * 3 ** 2 == 18")

    def test_precedence_add_power(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 + 3 ** 2 == 11")

    # --- Associativity ---

    def test_right_assoc_power(self, parser, evaluator):
        """2**3**2 = 2**(3**2) = 2**9 = 512, not (2**3)**2 = 64."""
        assert self._verify(parser, evaluator, "verify 2**3**2 == 512")

    def test_left_assoc_subtract(self, parser, evaluator):
        """10 - 3 - 2 = (10 - 3) - 2 = 5, not 10 - (3 - 2) = 9."""
        assert self._verify(parser, evaluator, "verify 10 - 3 - 2 == 5")

    def test_left_assoc_divide(self, parser, evaluator):
        """24 / 4 / 2 = (24 / 4) / 2 = 3.0, not 24 / (4 / 2) = 12.0."""
        assert self._verify(parser, evaluator, "verify 24 / 4 / 2 == 3.0")

    # --- Unary + power interaction ---

    def test_neg_power_python_convention(self, parser, evaluator):
        """-3**2 = -(3**2) = -9, Python convention."""
        assert self._verify(parser, evaluator, "verify -3**2 == -9")

    def test_power_neg_right(self, parser, evaluator):
        """2**-3 = 2**(-3) = 0.125."""
        assert self._verify(parser, evaluator, "verify 2**-3 == 0.125")

    # --- Edge cases ---

    def test_zero_power_zero(self, parser, evaluator):
        """0**0 = 1 (Python convention)."""
        assert self._verify(parser, evaluator, "verify 0**0 == 1")

    def test_division_by_zero(self, parser, evaluator):
        ast = parser.parse("verify 1 / 0 == 0")
        with pytest.raises(EvaluationError, match="Division by zero"):
            evaluator.evaluate(ast.body, {})

    def test_floor_division_by_zero(self, parser, evaluator):
        ast = parser.parse("verify 1 // 0 == 0")
        with pytest.raises(EvaluationError, match="Division by zero"):
            evaluator.evaluate(ast.body, {})

    def test_modulo_by_zero(self, parser, evaluator):
        ast = parser.parse("verify 1 % 0 == 0")
        with pytest.raises(EvaluationError, match="Division by zero"):
            evaluator.evaluate(ast.body, {})

    def test_large_exponent(self, parser, evaluator):
        """Large exponents produce correct results (Python arbitrary precision)."""
        assert self._verify(parser, evaluator, "verify 2 ** 100 == 1267650600228229401496703205376")

    def test_float_exponent_overflow(self, parser, evaluator):
        """Float exponentiation overflow raises EvaluationError."""
        ast = parser.parse("verify 2.0 ** 10000 == 0")
        with pytest.raises(EvaluationError, match="Arithmetic error"):
            evaluator.evaluate(ast.body, {})

    def test_unary_plus_minus(self, parser, evaluator):
        """+-3 parses as pos(neg(3)) = -3."""
        assert self._verify(parser, evaluator, "verify +-3 == -3")

    def test_unary_minus_plus(self, parser, evaluator):
        """-+3 parses as neg(pos(3)) = -3."""
        assert self._verify(parser, evaluator, "verify -+3 == -3")

    # --- Mixed with functions ---

    def test_function_plus_literal(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify tri(4) + 1 == 11")

    def test_function_times_literal(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify tri(4) * 2 == 20")

    def test_function_minus_function(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify primesum(7,2) - tri(36) == 0")

    def test_arithmetic_in_function_arg(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify pow(1 + 1, 10) == 1024")

    def test_complex_expression(self, parser, evaluator):
        """Multi-operator expression with functions."""
        assert self._verify(parser, evaluator, "verify (tri(4) + 1) * 2 - 1 == 21")

    def test_arithmetic_both_sides_comparison(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify 2 + 3 == 10 - 5")

    def test_namespaced_function_with_arithmetic(self, parser, evaluator):
        assert self._verify(parser, evaluator, "verify math.pow(2, 10) + 1 == 1025")


# =============================================================================
# Arithmetic Free Variable Tests
# =============================================================================

class TestArithmeticFreeVariables:
    """Test find_free_variables with arithmetic expressions."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_binary_op_with_variable(self, parser):
        expr = parser.parse("verify n + 1 == 5")
        assert find_free_variables(expr) == {'n'}

    def test_binary_op_two_variables(self, parser):
        expr = parser.parse("verify n + m == 5")
        assert find_free_variables(expr) == {'n', 'm'}

    def test_unary_variable(self, parser):
        expr = parser.parse("verify -n == 5")
        assert find_free_variables(expr) == {'n'}

    def test_no_variables_in_arithmetic(self, parser):
        expr = parser.parse("verify 2 + 3 == 5")
        assert find_free_variables(expr) == set()

    def test_variables_in_nested_arithmetic(self, parser):
        expr = parser.parse("verify (n + 1) * (m - 2) == 5")
        assert find_free_variables(expr) == {'n', 'm'}

    def test_variables_in_function_args_with_arithmetic(self, parser):
        expr = parser.parse("verify pow(n + 1, 2) == 5")
        assert find_free_variables(expr) == {'n'}

    def test_arithmetic_both_sides(self, parser):
        expr = parser.parse("verify n ** 2 == m + 1")
        assert find_free_variables(expr) == {'n', 'm'}


# =============================================================================
# Arithmetic Integration Tests (end-to-end with find_matches)
# =============================================================================

class TestArithmeticIntegration:
    """Test arithmetic expressions with the iteration engine."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_does_exist_n_squared(self, parser, evaluator):
        """does_exist n**2 == 25 should find n=5."""
        expr = parser.parse("does_exist n**2 == 25")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0]["n"] == 5

    def test_does_exist_with_addition(self, parser, evaluator):
        """does_exist (n + 1) * 2 == 10 should find n=4."""
        expr = parser.parse("does_exist (n + 1) * 2 == 10")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0]["n"] == 4

    def test_verify_arithmetic(self, parser, evaluator):
        expr = parser.parse("verify 2 ** 10 == 1024")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_verify_arithmetic_false(self, parser, evaluator):
        expr = parser.parse("verify 2 ** 10 == 999")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_for_any_with_arithmetic(self, parser, evaluator):
        """for_any n**2 == m finds pairs like (1,1), (2,4), (3,9)."""
        expr = parser.parse("for_any n**2 == m")
        matches = list(find_matches(expr, evaluator, {"n": 5, "m": 30}))
        assert len(matches) > 0
        for match in matches:
            assert match["n"] ** 2 == match["m"]

    def test_implicit_verify_arithmetic(self, parser, evaluator):
        """No quantifier + no free vars -> implicit verify."""
        expr = parser.parse("2 + 3 * 4 == 14")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_function_arithmetic_search(self, parser, evaluator):
        """does_exist tri(n) + 1 == 11 should find n=4 (tri(4)=10)."""
        expr = parser.parse("does_exist tri(n) + 1 == 11")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0]["n"] == 4

    def test_arithmetic_in_primesum_search(self, parser, evaluator):
        """does_exist primesum(n, 2) - 1 == 665 should find n=7."""
        expr = parser.parse("does_exist primesum(n, 2) - 1 == 665")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0]["n"] == 7

    def test_pemdas_all_operators(self, parser, evaluator):
        """PEMDAS stress test: every operator and unary minus in one expression.

        (1 + 2) ** 2 * 3 - 4 // 2 + 7 % 3 - -1 == 27

        Evaluation order:
          Parentheses:   (1+2) = 3
          Exponent:      3**2 = 9
          Multiply:      9*3 = 27
          Floor-divide:  4//2 = 2
          Modulo:        7%3 = 1
          Unary minus:   --1 = +1
          Add/Sub L→R:   27 - 2 + 1 + 1 = 27

        WolframAlpha: (1 + 2)^2 * 3 - Quotient[4, 2] + Mod[7, 3] - (-1)
        """
        expr = parser.parse("verify (1 + 2) ** 2 * 3 - 4 // 2 + 7 % 3 - -1 == 27")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_pemdas_nested_parens_and_right_assoc(self, parser, evaluator):
        """PEMDAS stress test: nested parentheses + right-associative **.

        ((2 + 3) * (7 - 4)) ** 2 // 9 + 2 ** 3 ** 1 - 15 % 4 == 30

        Evaluation order:
          Inner parens:  (2+3)=5, (7-4)=3
          Outer parens:  5*3 = 15
          Exponent:      15**2 = 225
          Right-assoc**: 2**(3**1) = 2**3 = 8
          Floor-divide:  225//9 = 25
          Modulo:        15%4 = 3
          Add/Sub L→R:   25 + 8 - 3 = 30

        WolframAlpha: Quotient[((2 + 3) * (7 - 4))^2, 9] + 2^(3^1) - Mod[15, 4]
        """
        expr = parser.parse(
            "verify ((2 + 3) * (7 - 4)) ** 2 // 9 + 2 ** 3 ** 1 - 15 % 4 == 30"
        )
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Expression Validation Tests
# =============================================================================

class TestValidation:
    """Test validate_expression() compile phase."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    def test_valid_expression(self, parser, registry):
        expr = parser.parse("verify primesum(7, 2) == 666")
        errors = validate_expression(expr, registry)
        assert errors == []

    def test_unknown_function(self, parser, registry):
        expr = parser.parse("verify bogus(7) == 666")
        errors = validate_expression(expr, registry)
        assert len(errors) == 1
        assert "Unknown function" in errors[0]
        assert "bogus" in errors[0]

    def test_valid_arithmetic(self, parser, registry):
        expr = parser.parse("verify 2 + 3 * 4 == 14")
        errors = validate_expression(expr, registry)
        assert errors == []

    def test_unknown_function_in_arithmetic(self, parser, registry):
        expr = parser.parse("verify bad_func(5) + 1 == 6")
        errors = validate_expression(expr, registry)
        assert len(errors) == 1
        assert "bad_func" in errors[0]

    def test_multiple_errors(self, parser, registry):
        expr = parser.parse("verify foo(1) + bar(2) == 3")
        errors = validate_expression(expr, registry)
        assert len(errors) == 2

    def test_valid_with_namespaced_function(self, parser, registry):
        expr = parser.parse("verify math.pow(2, 10) == 1024")
        errors = validate_expression(expr, registry)
        assert errors == []

    def test_unknown_namespaced_function(self, parser, registry):
        expr = parser.parse("verify fake.nope(1) == 1")
        errors = validate_expression(expr, registry)
        assert len(errors) == 1
        assert "fake.nope" in errors[0]


# =============================================================================
# Phase 3: Boolean Operator Tests
# =============================================================================

class TestBooleanAST:
    """Test boolean operator AST construction."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    def test_and_keyword(self, parser):
        """'and' produces BinaryOp with operator 'and'."""
        ast = parser.parse("verify 1 == 1 and 2 == 2")
        assert isinstance(ast.body, BinaryOp)
        assert ast.body.operator == 'and'

    def test_or_keyword(self, parser):
        """'or' produces BinaryOp with operator 'or'."""
        ast = parser.parse("verify 1 == 1 or 2 == 3")
        assert isinstance(ast.body, BinaryOp)
        assert ast.body.operator == 'or'

    def test_not_keyword(self, parser):
        """'not' produces UnaryOp with operator 'not'."""
        ast = parser.parse("verify not 1 == 2")
        assert isinstance(ast.body, UnaryOp)
        assert ast.body.operator == 'not'

    def test_symbolic_and(self, parser):
        """'&&' produces same AST as 'and'."""
        ast = parser.parse("verify 1 == 1 && 2 == 2")
        assert isinstance(ast.body, BinaryOp)
        assert ast.body.operator == 'and'

    def test_symbolic_or(self, parser):
        """'||' produces same AST as 'or'."""
        ast = parser.parse("verify 1 == 1 || 2 == 3")
        assert isinstance(ast.body, BinaryOp)
        assert ast.body.operator == 'or'

    def test_symbolic_not(self, parser):
        """'!' produces same AST as 'not'."""
        ast = parser.parse("verify ! 1 == 2")
        assert isinstance(ast.body, UnaryOp)
        assert ast.body.operator == 'not'


class TestBooleanEvaluation:
    """Test boolean operator evaluation including short-circuit."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_and_true_true(self, parser, evaluator):
        expr = parser.parse("verify 1 == 1 and 2 == 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_and_true_false(self, parser, evaluator):
        expr = parser.parse("verify 1 == 1 and 2 == 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_and_false_true(self, parser, evaluator):
        expr = parser.parse("verify 1 == 2 and 2 == 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_and_false_false(self, parser, evaluator):
        expr = parser.parse("verify 1 == 2 and 3 == 4")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_or_true_false(self, parser, evaluator):
        expr = parser.parse("verify 1 == 1 or 2 == 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_or_false_false(self, parser, evaluator):
        expr = parser.parse("verify 1 == 2 or 3 == 4")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_not_true(self, parser, evaluator):
        expr = parser.parse("verify not 1 == 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_not_false(self, parser, evaluator):
        expr = parser.parse("verify not 1 == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_short_circuit_and(self, parser, evaluator):
        """Short-circuit: 0 and (1/0) should NOT raise division by zero."""
        expr = parser.parse("verify 0 and 1 / 0 == 1")
        # 0 is falsy, so 'and' short-circuits before evaluating 1/0
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_short_circuit_or(self, parser, evaluator):
        """Short-circuit: 1 or (1/0) should NOT raise division by zero."""
        expr = parser.parse("verify 1 or 1 / 0 == 1")
        # 1 is truthy, so 'or' short-circuits before evaluating 1/0
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Phase 3: Bitwise Operator Tests
# =============================================================================

class TestBitwiseOperators:
    """Test bitwise operators (keyword and symbolic)."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_xor_keyword(self, parser, evaluator):
        """5 xor 3 == 6  (0b101 ^ 0b011 = 0b110)"""
        expr = parser.parse("verify 5 xor 3 == 6")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_band_keyword(self, parser, evaluator):
        """5 band 3 == 1  (0b101 & 0b011 = 0b001)"""
        expr = parser.parse("verify 5 band 3 == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_band_symbol(self, parser, evaluator):
        """5 & 3 == 1"""
        expr = parser.parse("verify (5 & 3) == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bor_keyword(self, parser, evaluator):
        """5 bor 3 == 7  (0b101 | 0b011 = 0b111)"""
        expr = parser.parse("verify 5 bor 3 == 7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bor_symbol(self, parser, evaluator):
        """5 | 3 == 7"""
        expr = parser.parse("verify (5 | 3) == 7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bitnot_symbol(self, parser, evaluator):
        """~0 == -1  (bitwise NOT of 0 in two's complement)"""
        expr = parser.parse("verify ~0 == -1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bitnot_keyword(self, parser, evaluator):
        """bnot 0 == -1"""
        expr = parser.parse("verify bnot 0 == -1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_shl_keyword(self, parser, evaluator):
        """1 shl 3 == 8  (1 << 3 = 8)"""
        expr = parser.parse("verify 1 shl 3 == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_shl_symbol(self, parser, evaluator):
        """1 << 3 == 8"""
        expr = parser.parse("verify (1 << 3) == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_shr_keyword(self, parser, evaluator):
        """8 shr 3 == 1  (8 >> 3 = 1)"""
        expr = parser.parse("verify 8 shr 3 == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_shr_symbol(self, parser, evaluator):
        """8 >> 3 == 1"""
        expr = parser.parse("verify (8 >> 3) == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_power_alias_caret(self, parser, evaluator):
        """^ is a power alias in default (num) context: 2^3 == 8."""
        expr = parser.parse("verify 2^3 == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_caret_equals_doublestar(self, parser, evaluator):
        """^ and ** produce same result in default context."""
        expr = parser.parse("verify 2^3 == 2**3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_nand_function(self, parser, evaluator):
        """nand(5, 3) == ~(5 & 3) == ~1 == -2"""
        expr = parser.parse("verify nand(5, 3) == -2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_nor_function(self, parser, evaluator):
        """nor(5, 3) == ~(5 | 3) == ~7 == -8"""
        expr = parser.parse("verify nor(5, 3) == -8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_xnor_function(self, parser, evaluator):
        """xnor(5, 3) == ~(5 ^ 3) == ~6 == -7"""
        expr = parser.parse("verify xnor(5, 3) == -7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Phase 3: Chained Comparison Tests
# =============================================================================

class TestChainedComparisons:
    """Test chained comparison expressions like 1 < x < 10."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_simple_chain_true(self, parser, evaluator):
        """1 < 2 < 3 is True."""
        expr = parser.parse("verify 1 < 2 < 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_simple_chain_false(self, parser, evaluator):
        """1 < 2 < 2 is False (2 < 2 fails)."""
        expr = parser.parse("verify 1 < 2 < 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_chain_three_ops(self, parser, evaluator):
        """1 < 2 < 3 < 4 is True."""
        expr = parser.parse("verify 1 < 2 < 3 < 4")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_chain_mixed_ops(self, parser, evaluator):
        """1 <= 2 < 3 is True."""
        expr = parser.parse("verify 1 <= 2 < 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_chain_eq(self, parser, evaluator):
        """5 == 5 == 5 is True."""
        expr = parser.parse("verify 5 == 5 == 5")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_backward_compat_single(self, parser, evaluator):
        """Single comparison n == 5 still works."""
        expr = parser.parse("does_exist n == 5")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert matches[0] == {"n": 5}

    def test_chain_with_variables(self, parser, evaluator):
        """does_exist 1 < n < 5 finds n=2,3,4."""
        expr = parser.parse("for_any 1 < n < 5")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 3
        found = {m["n"] for m in matches}
        assert found == {2, 3, 4}

    def test_chain_ast_structure(self, parser):
        """Chained comparison produces Comparison with list operands/operators."""
        ast = parser.parse("verify 1 < 2 < 3")
        assert isinstance(ast.body, Comparison)
        assert len(ast.body.operands) == 3
        assert len(ast.body.operators) == 2
        assert ast.body.operators == ["<", "<"]


# =============================================================================
# Phase 3: Precedence Tests
# =============================================================================

class TestPhase3Precedence:
    """Test cross-category precedence interactions."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_bool_lower_than_comparison(self, parser, evaluator):
        """1 < 2 and 3 > 1 → (1<2) and (3>1) → True"""
        expr = parser.parse("verify 1 < 2 and 3 > 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bitwise_between_compare_and_arith(self, parser, evaluator):
        """5 band 3 == 1 → (5&3) == 1 → True"""
        expr = parser.parse("verify 5 band 3 == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_shift_higher_than_bitor(self, parser, evaluator):
        """1 shl 3 bor 4 → (1<<3) | 4 → 8 | 4 → 12"""
        expr = parser.parse("verify 1 shl 3 bor 4 == 12")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_arith_higher_than_shift(self, parser, evaluator):
        """2 + 1 shl 3 → (2+1) << 3 → 3 << 3 → 24"""
        expr = parser.parse("verify 2 + 1 shl 3 == 24")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_power_highest_after_unary(self, parser, evaluator):
        """2^3 + 1 → (2**3) + 1 → 9"""
        expr = parser.parse("verify 2^3 + 1 == 9")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_not_lower_than_comparison(self, parser, evaluator):
        """not 1 < 2 → not (1<2) → not True → False"""
        expr = parser.parse("verify not 1 < 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_bitnot_higher_than_arith(self, parser, evaluator):
        """~0 + 1 → (~0) + 1 → -1 + 1 → 0"""
        expr = parser.parse("verify ~0 + 1 == 0")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_full_hierarchy_stress(self, parser, evaluator):
        """Complex expression using multiple precedence levels.
        1 < 2 and 5 band 3 bor 4 == 5 → (1<2) and (((5&3)|4) == 5) → True and (5==5) → True
        """
        expr = parser.parse("verify 1 < 2 and 5 band 3 bor 4 == 5")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Phase 3: Context Block Tests
# =============================================================================

class TestContextBlocks:
    """Test context block parsing and evaluation (num[], bit[], bool[])."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_bit_context_caret_xor(self, parser, evaluator):
        """bit[2^3] → XOR → 2 XOR 3 = 1"""
        expr = parser.parse("verify bit[2^3] == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_num_context_caret_power(self, parser, evaluator):
        """num[2^3] → power → 2**3 = 8"""
        expr = parser.parse("verify num[2^3] == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bit_context_and_bitwise(self, parser, evaluator):
        """bit[5 and 3] → bitwise AND → 5 & 3 = 1"""
        expr = parser.parse("verify bit[5 and 3] == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bit_context_or_bitwise(self, parser, evaluator):
        """bit[5 or 3] → bitwise OR → 5 | 3 = 7"""
        expr = parser.parse("verify bit[5 or 3] == 7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bit_context_not_bitwise(self, parser, evaluator):
        """bit[not 0] → bitwise NOT → ~0 = -1"""
        expr = parser.parse("verify bit[not 0] == -1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_mixed_contexts(self, parser, evaluator):
        """bit[2^3] + 1 → 1 + 1 → 2  (bit result converts to num)"""
        expr = parser.parse("verify bit[2^3] + 1 == 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_context_block_ast(self, parser):
        """Context block produces ContextBlock AST node."""
        ast = parser.parse("verify bit[5] == 5")
        # The body should be a Comparison, left side should be ContextBlock
        assert isinstance(ast.body, Comparison)
        assert isinstance(ast.body.operands[0], ContextBlock)
        assert ast.body.operands[0].context == "bit"

    def test_bool_context_explicit(self, parser, evaluator):
        """bool[1 and 1] → logical AND → True (1 is truthy)."""
        expr = parser.parse("verify bool[1 and 1]")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    # Issue #52: ^ precedence in bit[] context — fixed via contextual lexing
    # These tests verify that ^ parses at XOR precedence (level 6) inside
    # bit[...] rather than power precedence (level 12).

    def test_issue52_caret_xor_precedence_band_then_caret(self, parser, evaluator):
        """bit[2 band 3 ^ 4] → (2 & 3) ^ 4 = 2 ^ 4 = 6  (was: 2)"""
        expr = parser.parse("verify bit[2 band 3 ^ 4] == 6")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_caret_xor_precedence_caret_then_band(self, parser, evaluator):
        """bit[7 ^ 3 band 5] → 7 ^ (3 & 5) = 7 ^ 1 = 6  (was: 4)"""
        expr = parser.parse("verify bit[7 ^ 3 band 5] == 6")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_caret_xor_precedence_mixed_band_caret(self, parser, evaluator):
        """bit[7 band 5 ^ 6 band 3] → (7&5) ^ (6&3) = 5^2 = 7  (was: 3)"""
        expr = parser.parse("verify bit[7 band 5 ^ 6 band 3] == 7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_doublestar_always_power_in_bit(self, parser, evaluator):
        """** is always power, even inside bit[...]: bit[2**3] == 8"""
        expr = parser.parse("verify bit[2**3] == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_mixed_context_same_expression(self, parser, evaluator):
        """bit[2^3] + 2^3 → 1 + 8 = 9  (first ^ is XOR, second ^ is power)"""
        expr = parser.parse("verify bit[2^3] + 2^3 == 9")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_nested_context_inner_num(self, parser, evaluator):
        """bit[2 ^ num[2^3]] → 2 XOR 8 = 10  (inner ^ is power)"""
        expr = parser.parse("verify bit[2 ^ num[2^3]] == 10")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_caret_with_parens_in_bit(self, parser, evaluator):
        """Parens don't change context: bit[(2^3)] → XOR → 1"""
        expr = parser.parse("verify bit[(2^3)] == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_simple_caret_xor(self, parser, evaluator):
        """Simple case: bit[2^3] still works correctly as XOR."""
        expr = parser.parse("verify bit[2^3] == 1")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_caret_power_default(self, parser, evaluator):
        """Default (num) context: 2^3 == 8 still works."""
        expr = parser.parse("verify 2^3 == 8")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_issue52_xor_keyword_still_works(self, parser, evaluator):
        """xor keyword is unaffected by the change."""
        expr = parser.parse("verify bit[5 xor 3] == 6")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Phase 3: Free Variable Tests for New Operators
# =============================================================================

class TestPhase3FreeVariables:
    """Test free variable detection for boolean/bitwise/chained expressions."""

    def test_boolean_free_vars(self):
        comp1 = Comparison(operands=[Variable("n"), Literal(0)], operators=[">"])
        comp2 = Comparison(operands=[Variable("m"), Literal(10)], operators=["<"])
        expr = Expression(
            quantifier="for_any",
            body=BinaryOp(comp1, 'and', comp2)
        )
        assert find_free_variables(expr) == {"n", "m"}

    def test_bitwise_free_vars(self):
        node = BinaryOp(Variable("a"), 'xor', Variable("b"))
        assert find_free_variables(node) == {"a", "b"}

    def test_bitnot_free_vars(self):
        node = UnaryOp('~', Variable("x"))
        assert find_free_variables(node) == {"x"}

    def test_chained_comparison_free_vars(self):
        comp = Comparison(
            operands=[Literal(1), Variable("n"), Variable("m")],
            operators=["<", "<"]
        )
        assert find_free_variables(comp) == {"n", "m"}

    def test_context_block_free_vars(self):
        block = ContextBlock("bit", BinaryOp(Variable("x"), 'xor', Variable("y")))
        assert find_free_variables(block) == {"x", "y"}


# =============================================================================
# Phase 3: Integration Tests
# =============================================================================

class TestPhase3Integration:
    """End-to-end tests combining boolean/bitwise with existing features."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_boolean_with_find_matches(self, parser, evaluator):
        """does_exist n > 0 and n < 10 and tri(n) == 28 → n=7"""
        expr = parser.parse("does_exist n > 0 and n < 10 and tri(n) == 28")
        matches = list(find_matches(expr, evaluator, {"n": 20}))
        assert len(matches) == 1
        assert matches[0]["n"] == 7

    def test_boolean_verify(self, parser, evaluator):
        """verify 2 > 1 and 3 > 2 → True"""
        expr = parser.parse("verify 2 > 1 and 3 > 2")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_bitwise_with_find_matches(self, parser, evaluator):
        """does_exist n xor 3 == 6 → n=5 (because 5^3=6)"""
        expr = parser.parse("does_exist n xor 3 == 6")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0]["n"] == 5

    def test_chained_with_boolean(self, parser, evaluator):
        """does_exist 1 < n < 10 and tri(n) == 28 → n=7"""
        expr = parser.parse("does_exist 1 < n < 10 and tri(n) == 28")
        matches = list(find_matches(expr, evaluator, {"n": 20}))
        assert len(matches) == 1
        assert matches[0]["n"] == 7

    def test_keyword_variables_not_reserved(self, parser):
        """Variables like 'android', 'notable' still parse (longer than keywords)."""
        ast = parser.parse("does_exist android == 5")
        free = find_free_variables(ast)
        assert "android" in free

    def test_backward_compat_primesum(self, parser, evaluator):
        """Original use case still works: does_exist primesum(n,2) == 666"""
        expr = parser.parse("does_exist primesum(n,2) == 666")
        matches = list(find_matches(expr, evaluator, {"n": 100}))
        assert len(matches) == 1
        assert matches[0]["n"] == 7


# =============================================================================
# Complex Number Tests (Issue #54, Phase 1)
# =============================================================================

class TestComplexNumbers:
    """Tests for complex number support via function-first approach."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def _verify(self, parser, evaluator, expr_str):
        """Helper: parse and evaluate a verify expression, return comparison result."""
        ast = parser.parse(expr_str)
        return evaluator.evaluate(ast.body, {})

    # --- Basic function tests ---

    def test_complex_creation(self, parser, evaluator):
        """complex(3, 4) creates a non-zero complex number."""
        assert self._verify(parser, evaluator, "verify complex(3, 4) != 0")

    def test_complex_real(self, parser, evaluator):
        """real() extracts the real part."""
        assert self._verify(parser, evaluator, "verify real(complex(3, 4)) == 3")

    def test_complex_imag(self, parser, evaluator):
        """imag() extracts the imaginary part."""
        assert self._verify(parser, evaluator, "verify imag(complex(3, 4)) == 4")

    def test_complex_conjugate(self, parser, evaluator):
        """conj() returns the complex conjugate."""
        assert self._verify(parser, evaluator,
                            "verify conj(complex(3, 4)) == complex(3, -4)")

    def test_complex_abs_magnitude(self, parser, evaluator):
        """abs() returns magnitude: |3+4i| = 5."""
        assert self._verify(parser, evaluator, "verify abs(complex(3, 4)) == 5")

    # --- Arithmetic with complex ---

    def test_complex_addition(self, parser, evaluator):
        """(1+2i) + (3+4i) = (4+6i)."""
        assert self._verify(parser, evaluator,
                            "verify complex(1, 2) + complex(3, 4) == complex(4, 6)")

    def test_complex_subtraction(self, parser, evaluator):
        """(3+4i) - (1+2i) = (2+2i)."""
        assert self._verify(parser, evaluator,
                            "verify complex(3, 4) - complex(1, 2) == complex(2, 2)")

    def test_complex_multiplication(self, parser, evaluator):
        """(1+2i) * (3+4i) = (3+4+6i+8i^2) = (-5+10i)."""
        assert self._verify(parser, evaluator,
                            "verify complex(1, 2) * complex(3, 4) == complex(-5, 10)")

    def test_complex_conjugate_product(self, parser, evaluator):
        """z * conj(z) = |z|^2 = real number."""
        assert self._verify(parser, evaluator,
                            "verify complex(1, 2) * conj(complex(1, 2)) == 5")

    def test_complex_power_i_squared(self, parser, evaluator):
        """i^2 = -1."""
        assert self._verify(parser, evaluator,
                            "verify complex(0, 1) ** 2 == -1")

    # --- Equality and comparison ---

    def test_complex_equality(self, parser, evaluator):
        """Two identical complex numbers are equal."""
        assert self._verify(parser, evaluator,
                            "verify complex(3, 4) == complex(3, 4)")

    def test_complex_inequality(self, parser, evaluator):
        """Different complex numbers are not equal."""
        assert self._verify(parser, evaluator,
                            "verify complex(3, 4) != complex(4, 3)")

    def test_complex_ordering_error(self, parser, evaluator):
        """Ordering comparisons on complex numbers raise EvaluationError."""
        ast = parser.parse("verify complex(1, 2) < complex(3, 4)")
        with pytest.raises(EvaluationError, match="Cannot compare"):
            evaluator.evaluate(ast.body, {})

    # --- Edge cases ---

    def test_complex_real_of_real_number(self, parser, evaluator):
        """real() on a non-complex number returns the value itself."""
        assert self._verify(parser, evaluator, "verify real(5) == 5")

    def test_complex_imag_of_real_number(self, parser, evaluator):
        """imag() on a non-complex number returns 0."""
        assert self._verify(parser, evaluator, "verify imag(5) == 0")

    def test_complex_default_imag(self, parser, evaluator):
        """complex(5) with default imaginary part = 5+0i."""
        assert self._verify(parser, evaluator, "verify complex(5) == 5")

    def test_complex_division(self, parser, evaluator):
        """(1+0i) / (0+1i) = (0-1i) = -i."""
        assert self._verify(parser, evaluator,
                            "verify complex(1, 0) / complex(0, 1) == complex(0, -1)")

    def test_complex_floordiv_error(self, parser, evaluator):
        """Floor division on complex raises EvaluationError."""
        ast = parser.parse("verify complex(1, 2) // 1 == 0")
        with pytest.raises(EvaluationError, match="Unsupported operation"):
            evaluator.evaluate(ast.body, {})


# =============================================================================
# Imaginary Literal Tests (Issue #54, Phase 2)
# =============================================================================

class TestImaginaryLiterals:
    """Tests for imaginary literal syntax (e.g. 2ii, 3.5ii).

    Default config is 'none' (disabled). Tests use explicit suffix patterns.
    Configurable via imaginary_suffix_pattern parameter.
    """

    @pytest.fixture
    def parser_ii(self):
        """Parser with 'ii' suffix ([iI][iI])."""
        return ExpressionParser(imaginary_suffix_pattern='[iI][iI]')

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    @staticmethod
    def _verify(parser, evaluator, expr_str):
        ast = parser.parse(expr_str)
        return evaluator.evaluate(ast.body, {})

    # --- Parsing tests (with 'ii' suffix enabled) ---

    def test_parse_imaginary_ii(self, parser_ii):
        """2ii parses to Literal(complex(0, 2))."""
        ast = parser_ii.parse("verify 2ii == complex(0, 2)")
        assert isinstance(ast, Expression)

    def test_parse_imaginary_float(self, parser_ii):
        """3.5ii parses to Literal(complex(0, 3.5))."""
        ast = parser_ii.parse("verify 3.5ii == complex(0, 3.5)")
        assert isinstance(ast, Expression)

    def test_parse_imaginary_zero(self, parser_ii):
        """0ii parses to Literal(complex(0, 0))."""
        ast = parser_ii.parse("verify 0ii == 0")
        assert isinstance(ast, Expression)

    def test_parse_imaginary_mixed_case(self, parser_ii):
        """2iI also works (case-insensitive suffix)."""
        ast = parser_ii.parse("verify 2iI == complex(0, 2)")
        assert isinstance(ast, Expression)

    # --- Evaluation tests (with 'ii' suffix enabled) ---

    def test_imaginary_addition(self, parser_ii, evaluator):
        """3 + 2ii == complex(3, 2)."""
        assert self._verify(parser_ii, evaluator, "verify 3 + 2ii == complex(3, 2)")

    def test_imaginary_subtraction(self, parser_ii, evaluator):
        """3 - 2ii == complex(3, -2)."""
        assert self._verify(parser_ii, evaluator, "verify 3 - 2ii == complex(3, -2)")

    def test_imaginary_negation(self, parser_ii, evaluator):
        """-2ii == complex(0, -2)."""
        assert self._verify(parser_ii, evaluator, "verify -2ii == complex(0, -2)")

    def test_imaginary_squared(self, parser_ii, evaluator):
        """1ii ** 2 == -1 (i^2 = -1)."""
        assert self._verify(parser_ii, evaluator, "verify 1ii ** 2 == -1")

    def test_imaginary_abs(self, parser_ii, evaluator):
        """abs(3 + 4ii) == 5 (magnitude)."""
        assert self._verify(parser_ii, evaluator, "verify abs(3 + 4ii) == 5")

    def test_imaginary_conjugate_product(self, parser_ii, evaluator):
        """(1 + 2ii) * conj(1 + 2ii) == 5 (z * conj(z) = |z|^2)."""
        assert self._verify(parser_ii, evaluator,
                            "verify (1 + 2ii) * conj(complex(1, 2)) == 5")

    def test_imaginary_with_real_extraction(self, parser_ii, evaluator):
        """real(3 + 4ii) == 3."""
        assert self._verify(parser_ii, evaluator, "verify real(3 + 4ii) == 3")

    def test_imaginary_with_imag_extraction(self, parser_ii, evaluator):
        """imag(3 + 4ii) == 4."""
        assert self._verify(parser_ii, evaluator, "verify imag(3 + 4ii) == 4")

    def test_imaginary_multiplication(self, parser_ii, evaluator):
        """1ii * 1ii == -1 (i * i = -1)."""
        assert self._verify(parser_ii, evaluator, "verify 1ii * 1ii == -1")

    # --- Variable name preservation (with 'ii' suffix enabled) ---

    def test_variable_i_still_works(self, parser_ii, evaluator):
        """Standalone 'i' is a variable, not imaginary (even with ii suffix)."""
        ast = parser_ii.parse("does_exist i == 5")
        matches = list(find_matches(ast, evaluator, {'i': 10}))
        assert 5 in [m['i'] for m in matches]

    def test_variable_ii_still_works(self, parser_ii, evaluator):
        """Standalone 'ii' is a variable (IMAGINARY requires leading digit)."""
        ast = parser_ii.parse("does_exist ii == 5")
        matches = list(find_matches(ast, evaluator, {'ii': 10}))
        assert 5 in [m['ii'] for m in matches]

    # --- Config variants ---

    def test_single_i_suffix(self, evaluator):
        """Parser with '[iI]' pattern accepts 2i."""
        p = ExpressionParser(imaginary_suffix_pattern='[iI]')
        assert self._verify(p, evaluator, "verify 2i == complex(0, 2)")

    def test_single_j_suffix(self, evaluator):
        """Parser with '[jJ]' pattern accepts 2j."""
        p = ExpressionParser(imaginary_suffix_pattern='[jJ]')
        assert self._verify(p, evaluator, "verify 2j == complex(0, 2)")

    def test_both_suffixes(self, evaluator):
        """Parser with '[iIjJ]' pattern accepts both 2i and 2j."""
        p = ExpressionParser(imaginary_suffix_pattern='[iIjJ]')
        assert self._verify(p, evaluator, "verify 2i == 2j")

    def test_disabled_by_default(self):
        """Default parser has no IMAGINARY terminal."""
        p = ExpressionParser()  # default: imaginary_suffix_pattern=''
        with pytest.raises(ParseError):
            p.parse("verify 2ii == complex(0, 2)")

    def test_disabled_still_supports_complex_function(self, evaluator):
        """Default parser still supports complex() function (Phase 1)."""
        p = ExpressionParser()  # default: disabled
        assert self._verify(p, evaluator, "verify complex(3, 4) == complex(3, 4)")

    def test_ii_suffix_rejects_single_i(self, parser_ii):
        """'ii' parser does NOT accept single 'i' suffix (2i)."""
        with pytest.raises(ParseError):
            parser_ii.parse("verify 2i == complex(0, 2)")


# =============================================================================
# Sequence Enumeration Tests (Issue #36)
# =============================================================================

class TestSequenceEnumeration:
    """Tests for bare-term (no comparison) enumeration with for_any."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_for_any_bare_term_parses(self, parser):
        """Grammar accepts for_any with bare term (no comparison)."""
        ast = parser.parse("for_any primesum(n,2)")
        assert ast.quantifier == "for_any"
        assert isinstance(ast.body, FunctionCall)

    def test_for_any_bare_arithmetic_parses(self, parser):
        """Grammar accepts for_any with bare arithmetic expression."""
        ast = parser.parse("for_any n**2 + 1")
        assert ast.quantifier == "for_any"
        assert isinstance(ast.body, BinaryOp)

    def test_for_any_bare_term_enumerates_values(self, parser, evaluator):
        """for_any <bare term> yields {var: val, __value__: computed}."""
        expr = parser.parse("for_any n**2")
        matches = list(find_matches(expr, evaluator, {"n": 5}))
        assert len(matches) == 5
        assert matches[0] == {"n": 1, "__value__": 1}
        assert matches[1] == {"n": 2, "__value__": 4}
        assert matches[2] == {"n": 3, "__value__": 9}
        assert matches[3] == {"n": 4, "__value__": 16}
        assert matches[4] == {"n": 5, "__value__": 25}

    def test_for_any_bare_function_enumerates(self, parser, evaluator):
        """for_any primesum(n,2) enumerates computed values."""
        expr = parser.parse("for_any primesum(n,2)")
        matches = list(find_matches(expr, evaluator, {"n": 3}))
        assert len(matches) == 3
        # primesum(1,2) = 2^2 = 4
        assert matches[0]["n"] == 1
        assert matches[0]["__value__"] == 4
        # primesum(2,2) = 2^2 + 3^2 = 13
        assert matches[1]["n"] == 2
        assert matches[1]["__value__"] == 13

    def test_for_any_bare_multi_var(self, parser, evaluator):
        """for_any <bare term> with multiple free variables uses Cartesian product."""
        expr = parser.parse("for_any n + m")
        matches = list(find_matches(expr, evaluator, {"m": 2, "n": 2}))
        # Cartesian product: (m=1,n=1), (m=1,n=2), (m=2,n=1), (m=2,n=2)
        assert len(matches) == 4
        values = [(m["m"], m["n"], m["__value__"]) for m in matches]
        assert (1, 1, 2) in values
        assert (1, 2, 3) in values
        assert (2, 1, 3) in values
        assert (2, 2, 4) in values

    def test_for_any_comparison_unchanged(self, parser, evaluator):
        """for_any with comparison still works as before (boolean filter)."""
        expr = parser.parse("for_any n**2 == 9")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0] == {"n": 3}
        assert "__value__" not in matches[0]

    def test_for_any_bare_no_free_vars_error(self, parser, evaluator):
        """for_any with bare term but no free vars raises ValueError."""
        expr = parser.parse("for_any 2 + 3")
        with pytest.raises(ValueError, match="requires free variables"):
            list(find_matches(expr, evaluator, {}))

    def test_does_exist_bare_term_error(self, parser, evaluator):
        """does_exist with bare term (no comparison) raises ValueError."""
        expr = parser.parse("does_exist n**2")
        with pytest.raises(ValueError, match="requires a comparison"):
            list(find_matches(expr, evaluator, {"n": 10}))

    def test_verify_bare_term_truthy(self, parser, evaluator):
        """verify with bare term evaluates truthiness: nonzero → true."""
        expr = parser.parse("verify 7")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_verify_bare_term_falsy(self, parser, evaluator):
        """verify with bare term evaluates truthiness: zero → false."""
        expr = parser.parse("verify 0")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_verify_bare_function_truthy(self, parser, evaluator):
        """verify primesum(7,2) → true (666 is truthy)."""
        expr = parser.parse("verify primesum(7,2)")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_for_any_boolean_with_comparison_unchanged(self, parser, evaluator):
        """for_any with boolean AND containing comparisons still works."""
        expr = parser.parse("for_any n > 0 and n**2 == 9")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0] == {"n": 3}


# =============================================================================
# Solve Directive Tests (Issue #51 Phase 1)
# =============================================================================

class TestSolveDirective:
    """Tests for the solve directive (calculator mode, enumeration, search)."""

    @pytest.fixture
    def parser(self):
        return ExpressionParser()

    @pytest.fixture
    def registry(self):
        return FunctionRegistry()

    @pytest.fixture
    def evaluator(self, registry):
        return ExpressionEvaluator(registry)

    def test_solve_parses(self, parser):
        """Grammar accepts solve keyword."""
        ast = parser.parse("solve (1 + 2) ** 2")
        assert ast.quantifier == "solve"

    def test_solve_calculator_mode(self, parser, evaluator):
        """solve <bare term> with no free vars → calculator mode."""
        expr = parser.parse("solve (1 + 2) ** 2 * 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert len(matches) == 1
        assert matches[0]["__solve_result__"] == 27

    def test_solve_calculator_function(self, parser, evaluator):
        """solve primesum(7,2) → 666."""
        expr = parser.parse("solve primesum(7,2)")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__solve_result__"] == 666

    def test_solve_verify_mode(self, parser, evaluator):
        """solve <comparison> with no free vars → verify-like truth check."""
        expr = parser.parse("solve primesum(7,2) == 666")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True

    def test_solve_verify_false(self, parser, evaluator):
        """solve <comparison> false case."""
        expr = parser.parse("solve 2 + 2 == 5")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is False

    def test_solve_enumeration_mode(self, parser, evaluator):
        """solve <bare term> with free vars → value enumeration."""
        expr = parser.parse("solve n ** 2")
        matches = list(find_matches(expr, evaluator, {"n": 4}))
        assert len(matches) == 4
        assert matches[0] == {"n": 1, "__value__": 1}
        assert matches[1] == {"n": 2, "__value__": 4}
        assert matches[2] == {"n": 3, "__value__": 9}
        assert matches[3] == {"n": 4, "__value__": 16}

    def test_solve_comparison_with_free_vars(self, parser, evaluator):
        """solve <comparison> with free vars → brute-force search (like does_exist)."""
        expr = parser.parse("solve n ** 2 == 25")
        matches = list(find_matches(expr, evaluator, {"n": 10}))
        assert len(matches) == 1
        assert matches[0] == {"n": 5}

    def test_implicit_calculator_mode(self, parser, evaluator):
        """No quantifier + bare term + no free vars → implicit solve."""
        expr = parser.parse("(1 + 2) ** 2 * 3")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__solve_result__"] == 27

    def test_implicit_calculator_function(self, parser, evaluator):
        """primesum(7,2) with no quantifier → implicit solve → 666."""
        expr = parser.parse("primesum(7,2)")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__solve_result__"] == 666

    def test_implicit_verify_unchanged(self, parser, evaluator):
        """No quantifier + comparison + no free vars → still implicit verify."""
        expr = parser.parse("primesum(7,2) == 666")
        matches = list(find_matches(expr, evaluator, {}))
        assert matches[0]["__verify_result__"] is True


# =============================================================================
# Format Match Tests for New Output Modes
# =============================================================================

class TestFormatMatchNewModes:
    """Tests for format_match with solve/calculator and value enumeration output."""

    def test_solve_result_text(self):
        from utils.cli import format_match
        result = format_match({"__solve_result__": 27}, "text")
        assert result == "27"

    def test_solve_result_json(self):
        import json
        from utils.cli import format_match
        result = format_match({"__solve_result__": 666}, "json")
        parsed = json.loads(result)
        assert parsed["result"] == 666

    def test_solve_result_csv(self):
        from utils.cli import format_match
        result = format_match({"__solve_result__": 42}, "csv")
        assert result == "42"

    def test_value_enumeration_text(self):
        from utils.cli import format_match
        result = format_match({"n": 3, "__value__": 9}, "text")
        assert result == "n=3: 9"

    def test_value_enumeration_json(self):
        import json
        from utils.cli import format_match
        result = format_match({"n": 3, "__value__": 9}, "json")
        parsed = json.loads(result)
        assert parsed["variables"] == {"n": 3}
        assert parsed["value"] == 9

    def test_value_enumeration_csv(self):
        from utils.cli import format_match
        result = format_match({"n": 3, "__value__": 9}, "csv")
        assert result == "3,9"

    def test_value_enumeration_multi_var_text(self):
        from utils.cli import format_match
        result = format_match({"m": 2, "n": 3, "__value__": 5}, "text")
        assert result == "m=2, n=3: 5"

    def test_value_enumeration_multi_var_csv(self):
        from utils.cli import format_match
        result = format_match({"m": 2, "n": 3, "__value__": 5}, "csv")
        assert result == "2,3,5"
