"""
Expression parser and evaluator for mathematical queries.
==========================================================

Provides:
- AST classes for expression representation
- Lark-based parser for expression grammar
- Evaluator with FunctionRegistry integration
- Iteration engine for multi-variable expressions

Target syntax examples:
    does_exist primesum(n,2) == 666
    for_any primesum(n,2) == tri(m)
    verify primesum(7,2) == 666
    primesum(7,2) == 666              # implicit verify (no free vars)

Issue: #17 (Expression parser with AST)
Epic: #13 (Generalized Expression Grammar)
"""

from __future__ import annotations

import itertools
from abc import ABC
from dataclasses import dataclass
from typing import Any, Callable, Dict, Iterator, List, Optional, Set, Union

from lark import Lark, Transformer
from lark.visitors import v_args
from lark.exceptions import UnexpectedInput, UnexpectedCharacters, UnexpectedToken

from utils.function_registry import FunctionRegistry
from utils.iterators import IntIterator, SequenceIterator


# =============================================================================
# AST Classes
# =============================================================================

@dataclass
class ASTNode(ABC):
    """Base class for all AST nodes."""
    pass


@dataclass
class Literal(ASTNode):
    """A literal numeric value (int or float)."""
    value: Union[int, float]


@dataclass
class Variable(ASTNode):
    """A variable reference (unbound identifier)."""
    name: str


@dataclass
class FunctionCall(ASTNode):
    """A function call with arguments."""
    name: str
    args: List[ASTNode]


@dataclass
class Comparison(ASTNode):
    """A comparison between two terms."""
    left: ASTNode
    operator: str  # ==, !=, <, >, <=, >=
    right: ASTNode


@dataclass
class Expression(ASTNode):
    """A complete expression with quantifier and comparison."""
    quantifier: Optional[str]  # "for_any", "does_exist", "verify", or None (auto-detect)
    comparison: Comparison


# =============================================================================
# Lark Grammar
# =============================================================================

GRAMMAR = r"""
    start: [quantifier] comparison

    quantifier: "for_any" -> for_any
              | "does_exist" -> does_exist
              | "verify" -> verify

    comparison: term COMP_OP term

    COMP_OP: "==" | "!=" | "<=" | ">=" | "<" | ">"

    term: function_call
        | literal
        | variable

    function_call: NAME "(" [args] ")"
    args: term ("," term)*

    literal: NUMBER
    variable: NAME

    NAME: /[a-zA-Z_][a-zA-Z0-9_]*(\.[a-zA-Z_][a-zA-Z0-9_]*)*/
    NUMBER: /[0-9]+(\.[0-9]+)?/

    %import common.WS
    %ignore WS
"""


# =============================================================================
# AST Transformer (Lark parse tree -> dataclasses)
# =============================================================================

@v_args(inline=True)
class ASTTransformer(Transformer):
    """Transform Lark parse tree into AST dataclasses."""

    def start(self, *args) -> Expression:
        if len(args) == 2:
            quantifier, comparison = args
        else:
            # No quantifier specified - will be auto-detected in find_matches
            comparison = args[0]
            quantifier = None
        return Expression(quantifier=quantifier, comparison=comparison)

    def for_any(self) -> str:
        return "for_any"

    def does_exist(self) -> str:
        return "does_exist"

    def verify(self) -> str:
        return "verify"

    def comparison(self, left: ASTNode, op, right: ASTNode) -> Comparison:
        return Comparison(left=left, operator=str(op), right=right)

    def term(self, child: ASTNode) -> ASTNode:
        """Unwrap term rule - just returns its single child."""
        return child

    def function_call(self, name, *args_or_none) -> FunctionCall:
        # args_or_none is either empty or contains a list of args
        if args_or_none and isinstance(args_or_none[0], list):
            args = args_or_none[0]
        else:
            args = []
        return FunctionCall(name=str(name), args=args)

    def args(self, *terms) -> List[ASTNode]:
        return list(terms)

    def literal(self, value) -> Literal:
        v = float(value) if '.' in str(value) else int(value)
        return Literal(value=v)

    def variable(self, name) -> Variable:
        return Variable(name=str(name))


# =============================================================================
# Parse Error Handling
# =============================================================================

class ParseError(Exception):
    """Custom exception for expression parse errors with helpful messages."""

    def __init__(self, message: str, original: Optional[Exception] = None):
        super().__init__(message)
        self.original = original


def _format_parse_error(e: Exception, text: str) -> str:
    """Convert Lark exception to user-friendly message."""
    if isinstance(e, UnexpectedCharacters):
        return (
            f"Unexpected character at position {e.column}: '{text[e.column-1] if e.column <= len(text) else '?'}'\n"
            f"  {text}\n"
            f"  {' ' * (e.column - 1)}^"
        )
    elif isinstance(e, UnexpectedToken):
        return (
            f"Unexpected token '{e.token}' at position {e.column}\n"
            f"  Expected one of: {', '.join(str(x) for x in e.expected)}"
        )
    elif isinstance(e, UnexpectedInput):
        return f"Invalid expression syntax: {str(e)}"
    else:
        return f"Parse error: {str(e)}"


# =============================================================================
# Expression Parser
# =============================================================================

class ExpressionParser:
    """
    Parser for mathematical query expressions.

    Uses Lark to parse expressions into an AST of dataclasses.
    Parse once, evaluate many times.

    Example:
        parser = ExpressionParser()
        ast = parser.parse("does_exist primesum(n,2) == 666")
    """

    def __init__(self):
        self._parser = Lark(
            GRAMMAR,
            parser='lalr',
            transformer=ASTTransformer()
        )

    def parse(self, text: str) -> Expression:
        """
        Parse an expression string into an AST.

        Args:
            text: Expression string like "does_exist primesum(n,2) == 666"

        Returns:
            Expression AST node

        Raises:
            ParseError: If the expression is syntactically invalid
        """
        text = text.strip()
        if not text:
            raise ParseError("Empty expression")

        try:
            return self._parser.parse(text)
        except (UnexpectedInput, UnexpectedCharacters, UnexpectedToken) as e:
            raise ParseError(_format_parse_error(e, text), original=e)
        except Exception as e:
            raise ParseError(f"Parse error: {str(e)}", original=e)


# =============================================================================
# Free Variable Detection
# =============================================================================

def find_free_variables(node: ASTNode) -> Set[str]:
    """
    Find all unbound variable names in an AST.

    Args:
        node: AST node to search

    Returns:
        Set of variable names found in the expression
    """
    if isinstance(node, Literal):
        return set()
    elif isinstance(node, Variable):
        return {node.name}
    elif isinstance(node, FunctionCall):
        result: Set[str] = set()
        for arg in node.args:
            result |= find_free_variables(arg)
        return result
    elif isinstance(node, Comparison):
        return find_free_variables(node.left) | find_free_variables(node.right)
    elif isinstance(node, Expression):
        return find_free_variables(node.comparison)
    return set()


# =============================================================================
# Expression Evaluator
# =============================================================================

class EvaluationError(Exception):
    """Exception raised during expression evaluation."""
    pass


class ExpressionEvaluator:
    """
    Evaluates AST nodes using a FunctionRegistry.

    Example:
        registry = FunctionRegistry()
        evaluator = ExpressionEvaluator(registry)
        result = evaluator.evaluate(ast.comparison, {'n': 7})
    """

    def __init__(self, registry: FunctionRegistry):
        self.registry = registry

    def evaluate(self, node: ASTNode, context: Dict[str, Any]) -> Any:
        """
        Evaluate an AST node with given variable bindings.

        Args:
            node: AST node to evaluate
            context: Variable name -> value mapping

        Returns:
            Evaluation result (number for terms, bool for comparisons)

        Raises:
            EvaluationError: If evaluation fails
        """
        if isinstance(node, Literal):
            return node.value

        elif isinstance(node, Variable):
            if node.name not in context:
                raise EvaluationError(f"Unbound variable: '{node.name}'")
            return context[node.name]

        elif isinstance(node, FunctionCall):
            try:
                func = self.registry.get(node.name)
            except ValueError as e:
                raise EvaluationError(str(e))

            args = [self.evaluate(arg, context) for arg in node.args]
            try:
                return func(*args)
            except Exception as e:
                raise EvaluationError(
                    f"Error calling {node.name}({', '.join(str(a) for a in args)}): {e}"
                )

        elif isinstance(node, Comparison):
            left = self.evaluate(node.left, context)
            right = self.evaluate(node.right, context)
            return self._compare(left, node.operator, right)

        elif isinstance(node, Expression):
            return self.evaluate(node.comparison, context)

        else:
            raise EvaluationError(f"Unknown AST node type: {type(node).__name__}")

    def _compare(self, left: Any, op: str, right: Any) -> bool:
        """Perform a comparison operation."""
        ops = {
            "==": lambda a, b: a == b,
            "!=": lambda a, b: a != b,
            "<": lambda a, b: a < b,
            ">": lambda a, b: a > b,
            "<=": lambda a, b: a <= b,
            ">=": lambda a, b: a >= b,
        }
        if op not in ops:
            raise EvaluationError(f"Unknown comparison operator: '{op}'")
        return ops[op](left, right)


# =============================================================================
# Iteration Engine
# =============================================================================

def find_matches(
    expr: Expression,
    evaluator: ExpressionEvaluator,
    bounds: Dict[str, int],
    iterator_factories: Optional[Dict[str, Callable[[], SequenceIterator]]] = None
) -> Iterator[Dict[str, Any]]:
    """
    Find all variable assignments that satisfy the expression.

    For does_exist quantifier, yields the first match and stops.
    For for_any quantifier, yields all matches.
    For verify quantifier (or auto-detected), yields {"__verify_result__": bool}.

    Args:
        expr: Parsed expression with quantifier
        evaluator: Expression evaluator with function registry
        bounds: Max values for each free variable {var_name: max_value}
            Used when iterator_factories doesn't specify a factory for a variable.
        iterator_factories: Optional dict mapping variable names to factory
            functions that return SequenceIterator instances. Takes precedence
            over bounds for the same variable.

    Yields:
        Dict mapping variable names to values that satisfy comparison,
        or {"__verify_result__": bool} for verify mode

    Raises:
        ValueError: If a free variable has no bound or iterator specified
        ValueError: If verify mode is used with free variables
        ValueError: If no quantifier and expression has free variables

    Example:
        parser = ExpressionParser()
        registry = FunctionRegistry()
        evaluator = ExpressionEvaluator(registry)

        # Using bounds (backwards compatible)
        expr = parser.parse("does_exist primesum(n,2) == 666")
        for match in find_matches(expr, evaluator, {'n': 100}):
            print(match)  # {'n': 7}

        # Using iterator_factories
        from utils.iterators import IntIterator
        expr = parser.parse("for_any primesum(n,2) == tri(m)")
        for match in find_matches(expr, evaluator, {}, {
            'n': lambda: IntIterator(1, 100, 2),  # odd numbers only
            'm': lambda: IntIterator(1, 50)
        }):
            print(match)

        # Verify mode
        expr = parser.parse("verify primesum(7,2) == 666")
        for match in find_matches(expr, evaluator, {}):
            print(match)  # {'__verify_result__': True}
    """
    free_vars = find_free_variables(expr)
    quantifier = expr.quantifier

    # Auto-detect quantifier when not specified
    if quantifier is None:
        if free_vars:
            raise ValueError(
                f"Expression has free variables ({', '.join(sorted(free_vars))}) but no quantifier. "
                f"Use 'does_exist' or 'for_any' prefix, e.g.: does_exist {expr.comparison}"
            )
        # No free vars and no quantifier -> implicit verify mode
        quantifier = "verify"

    # Validate verify mode - must have no free variables
    if quantifier == "verify":
        if free_vars:
            raise ValueError(
                f"'verify' requires a closed formula (no free variables), "
                f"but found: {', '.join(sorted(free_vars))}"
            )
        # Evaluate and yield result
        result = evaluator.evaluate(expr.comparison, {})
        yield {"__verify_result__": bool(result)}
        return

    # Initialize iterator_factories if not provided
    if iterator_factories is None:
        iterator_factories = {}

    # Validate all free variables have bounds or iterator factories (for does_exist / for_any)
    covered_vars = set(bounds.keys()) | set(iterator_factories.keys())
    missing = free_vars - covered_vars
    if missing:
        missing_list = sorted(missing)
        suggestions = ', '.join(f'--max-{v}' for v in missing_list)
        raise ValueError(
            f"Missing bounds for variable(s): {', '.join(missing_list)}. "
            f"Use {suggestions} to specify."
        )

    # Handle no-variable case for does_exist/for_any (e.g., "does_exist tri(4) == 10")
    if not free_vars:
        if evaluator.evaluate(expr.comparison, {}):
            yield {}
        return

    # Build iterators for each variable
    # iterator_factories takes precedence over bounds
    var_list = sorted(free_vars)
    iterators = []
    for v in var_list:
        if v in iterator_factories:
            iterators.append(iterator_factories[v]())
        else:
            # Default: IntIterator from 1 to bounds[v]
            iterators.append(IntIterator(1, bounds[v], 1))

    # Generate all combinations (Cartesian product)
    # Note: itertools.product needs iterables, so we convert iterators to lists
    # Future Phase 5 will add parallel/clamp/wrap strategies that don't materialize lists
    ranges = [list(it) for it in iterators]

    # Track if we've validated functions (do this on first iteration)
    functions_validated = False

    for values in itertools.product(*ranges):
        context = dict(zip(var_list, values))
        try:
            if evaluator.evaluate(expr.comparison, context):
                yield context.copy()
                if quantifier == "does_exist":
                    return  # Stop at first match
            functions_validated = True  # If we got here, functions are valid
        except EvaluationError as e:
            # Check if this is a fatal error (unknown function, etc.)
            # vs a skippable error (invalid args during iteration)
            error_msg = str(e).lower()
            if "unknown function" in error_msg or not functions_validated:
                # First iteration error or unknown function: re-raise
                raise
            # Skip combinations that cause evaluation errors
            # (e.g., primesum(-1, 2) when iteration produces invalid args)
            continue


def verify_expression(
    expr: Expression,
    evaluator: ExpressionEvaluator
) -> bool:
    """
    Evaluate a closed-formula expression and return boolean result.

    Convenience function for verify mode that returns a simple boolean
    instead of an iterator.

    Args:
        expr: Parsed expression (should have no free variables)
        evaluator: Expression evaluator with function registry

    Returns:
        True if the expression evaluates to true, False otherwise

    Raises:
        ValueError: If expression has free variables

    Example:
        expr = parser.parse("verify primesum(7,2) == 666")
        result = verify_expression(expr, evaluator)  # True
    """
    free_vars = find_free_variables(expr)
    if free_vars:
        raise ValueError(
            f"verify_expression requires closed formula, "
            f"but found free variables: {', '.join(sorted(free_vars))}"
        )
    return bool(evaluator.evaluate(expr.comparison, {}))
