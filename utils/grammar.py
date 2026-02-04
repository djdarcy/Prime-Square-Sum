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
    does_exist tri(n) == trisum(qtri(666))

Issue: #17 (Expression parser with AST)
Epic: #13 (Generalized Expression Grammar)
"""

from __future__ import annotations

import itertools
from abc import ABC
from dataclasses import dataclass
from typing import Any, Dict, Iterator, List, Optional, Set, Union

from lark import Lark, Transformer
from lark.visitors import v_args
from lark.exceptions import UnexpectedInput, UnexpectedCharacters, UnexpectedToken

from utils.function_registry import FunctionRegistry


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
    quantifier: str  # "for_any" or "does_exist"
    comparison: Comparison


# =============================================================================
# Lark Grammar
# =============================================================================

GRAMMAR = r"""
    start: quantifier comparison

    quantifier: "for_any" -> for_any
              | "does_exist" -> does_exist

    comparison: term COMP_OP term

    COMP_OP: "==" | "!=" | "<=" | ">=" | "<" | ">"

    term: function_call
        | literal
        | variable

    function_call: NAME "(" [args] ")"
    args: term ("," term)*

    literal: NUMBER
    variable: NAME

    NAME: /[a-zA-Z_][a-zA-Z0-9_]*/
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

    def start(self, quantifier: str, comparison: Comparison) -> Expression:
        return Expression(quantifier=quantifier, comparison=comparison)

    def for_any(self) -> str:
        return "for_any"

    def does_exist(self) -> str:
        return "does_exist"

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
    bounds: Dict[str, int]
) -> Iterator[Dict[str, int]]:
    """
    Find all variable assignments that satisfy the expression.

    For does_exist quantifier, yields the first match and stops.
    For for_any quantifier, yields all matches.

    Args:
        expr: Parsed expression with quantifier
        evaluator: Expression evaluator with function registry
        bounds: Max values for each free variable {var_name: max_value}

    Yields:
        Dict mapping variable names to values that satisfy comparison

    Raises:
        ValueError: If a free variable has no bound specified

    Example:
        parser = ExpressionParser()
        registry = FunctionRegistry()
        evaluator = ExpressionEvaluator(registry)

        expr = parser.parse("does_exist primesum(n,2) == 666")
        for match in find_matches(expr, evaluator, {'n': 100}):
            print(match)  # {'n': 7}
    """
    free_vars = find_free_variables(expr)

    # Validate all free variables have bounds
    missing = free_vars - set(bounds.keys())
    if missing:
        missing_list = sorted(missing)
        suggestions = ', '.join(f'--max-{v}' for v in missing_list)
        raise ValueError(
            f"Missing bounds for variable(s): {', '.join(missing_list)}. "
            f"Use {suggestions} to specify."
        )

    # Handle no-variable case (e.g., "does_exist tri(4) == 10")
    if not free_vars:
        if evaluator.evaluate(expr.comparison, {}):
            yield {}
        return

    # Generate all combinations within bounds
    var_list = sorted(free_vars)
    ranges = [range(1, bounds[v] + 1) for v in var_list]

    for values in itertools.product(*ranges):
        context = dict(zip(var_list, values))
        try:
            if evaluator.evaluate(expr.comparison, context):
                yield context.copy()
                if expr.quantifier == "does_exist":
                    return  # Stop at first match
        except EvaluationError:
            # Skip combinations that cause evaluation errors
            # (e.g., primesum(-1, 2) when iteration somehow produces invalid args)
            continue
