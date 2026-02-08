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
import operator as op_module
from abc import ABC
from dataclasses import dataclass
from typing import Any, Callable, Dict, Iterator, List, Optional, Set, Union

from lark import Lark, Token, Transformer
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
    """A comparison (possibly chained) between terms.

    Single:  Comparison(operands=[a, b], operators=["=="])
    Chained: Comparison(operands=[a, b, c], operators=["<", "<"])
    """
    operands: List[ASTNode]
    operators: List[str]  # ==, !=, <, >, <=, >=


@dataclass
class BinaryOp(ASTNode):
    """Binary arithmetic operation: left OP right."""
    left: ASTNode
    operator: str  # +, -, *, /, //, %, **
    right: ASTNode


@dataclass
class UnaryOp(ASTNode):
    """Unary operation: OP operand."""
    operator: str  # -, +
    operand: ASTNode


@dataclass
class ContextBlock(ASTNode):
    """A context block that changes operator interpretation.

    Contexts: "num" (default/math), "bit" (bitwise), "bool" (boolean/logical).
    """
    context: str    # "num", "bit", or "bool"
    body: ASTNode


@dataclass
class Expression(ASTNode):
    """A complete expression with quantifier and body."""
    quantifier: Optional[str]  # "for_any", "does_exist", "verify", or None (auto-detect)
    body: ASTNode


# =============================================================================
# Lark Grammar
# =============================================================================

GRAMMAR = r"""
    start: [quantifier] body

    quantifier: "for_any" -> for_any
              | "does_exist" -> does_exist
              | "verify" -> verify

    // Precedence hierarchy (lowest → highest binding):
    //   1.  or, ||                     (logical OR, left-assoc)
    //   2.  and, &&                    (logical AND, left-assoc)
    //   3.  not, !                     (logical NOT, unary prefix)
    //   4.  ==, !=, <, >, <=, >=      (comparison, chainable)
    //   5.  bor, |                     (bitwise OR, left-assoc)
    //   6.  xor, ^ (in bit context)   (bitwise XOR, left-assoc)
    //   7.  band, &                    (bitwise AND, left-assoc)
    //   8.  shl/<<, shr/>>            (bit shifts, left-assoc)
    //   9.  +, -                       (addition, left-assoc)
    //  10.  *, /, //, %               (multiplication, left-assoc)
    //  11.  -x, +x, ~, bnot          (unary prefix)
    //  12.  **, ^ (in num context)    (exponentiation, right-assoc)
    //  13.  atoms, context blocks     (terminals)

    // Virtual tokens: CARET is matched by lexer, then transformed
    // via lexer_callbacks into CARET_AS_POWER or CARET_AS_XOR
    // based on context stack (num vs bit).
    %declare CARET_AS_POWER CARET_AS_XOR

    ?body: or_expr

    ?or_expr: and_expr
            | or_expr "or" and_expr     -> lor
            | or_expr "||" and_expr     -> lor

    ?and_expr: not_expr
             | and_expr "and" not_expr  -> land
             | and_expr "&&" not_expr   -> land

    ?not_expr: comparison
             | "not" not_expr           -> lnot
             | "!" not_expr             -> lnot

    ?comparison: bitor_expr (COMP_OP bitor_expr)*

    COMP_OP: "==" | "!=" | "<=" | ">=" | "<" | ">"
    SHL_OP.2: "<<"
    SHR_OP.2: ">>"

    ?bitor_expr: bitxor_expr
               | bitor_expr "bor" bitxor_expr   -> bitor
               | bitor_expr "|" bitxor_expr     -> bitor

    ?bitxor_expr: bitand_expr
                | bitxor_expr "xor" bitand_expr -> bitxor
                | bitxor_expr CARET_AS_XOR bitand_expr -> bitxor

    ?bitand_expr: shift_expr
                | bitand_expr "band" shift_expr -> bitand
                | bitand_expr "&" shift_expr    -> bitand

    ?shift_expr: add_expr
               | shift_expr "shl" add_expr      -> shl
               | shift_expr SHL_OP add_expr     -> shl
               | shift_expr "shr" add_expr      -> shr
               | shift_expr SHR_OP add_expr     -> shr

    ?add_expr: mul_expr
             | add_expr "+" mul_expr   -> add
             | add_expr "-" mul_expr   -> sub

    ?mul_expr: unary_expr
             | mul_expr "*" unary_expr    -> mul
             | mul_expr "/" unary_expr    -> div
             | mul_expr "//" unary_expr   -> floordiv
             | mul_expr "%" unary_expr    -> mod_op

    ?unary_expr: power_expr
               | "-" unary_expr    -> neg
               | "+" unary_expr    -> pos
               | "~" unary_expr    -> bitnot
               | "bnot" unary_expr -> bitnot

    ?power_expr: atom
               | atom "**" unary_expr          -> power
               | atom CARET_AS_POWER unary_expr -> power

    ?atom: function_call
         | context_block
         | literal
         | variable
         | "(" body ")"

    function_call: NAME "(" [args] ")"
    args: body ("," body)*

    context_block: CTX_NUM_OPEN body RBRACK   -> ctx_num
                 | CTX_BIT_OPEN body RBRACK   -> ctx_bit
                 | CTX_BOOL_OPEN body RBRACK  -> ctx_bool

    literal: NUMBER
    variable: NAME

    // Context-tracking terminals (matched before NAME due to higher priority)
    CTX_NUM_OPEN.3: /num\[/
    CTX_BIT_OPEN.3: /bit\[/
    CTX_BOOL_OPEN.3: /bool\[/
    RBRACK: "]"
    CARET: "^"

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
            quantifier, body = args
        else:
            # No quantifier specified - will be auto-detected in find_matches
            body = args[0]
            quantifier = None
        return Expression(quantifier=quantifier, body=body)

    def for_any(self) -> str:
        return "for_any"

    def does_exist(self) -> str:
        return "does_exist"

    def verify(self) -> str:
        return "verify"

    def comparison(self, *args) -> Comparison:
        # args = [operand1, op1, operand2, op2, operand3, ...]
        operands = [args[i] for i in range(0, len(args), 2)]
        operators = [str(args[i]) for i in range(1, len(args), 2)]
        return Comparison(operands=operands, operators=operators)

    # Boolean operators -> BinaryOp / UnaryOp
    def lor(self, left, right):      return BinaryOp(left, 'or', right)
    def land(self, left, right):     return BinaryOp(left, 'and', right)
    def lnot(self, operand):         return UnaryOp('not', operand)

    # Bitwise operators -> BinaryOp / UnaryOp
    def bitor(self, left, right):    return BinaryOp(left, 'bor', right)
    def bitxor(self, *args):
        nodes = [a for a in args if not isinstance(a, Token)]
        return BinaryOp(nodes[0], 'xor', nodes[1])
    def bitand(self, left, right):   return BinaryOp(left, 'band', right)
    def shl(self, *args):
        nodes = [a for a in args if not isinstance(a, Token)]
        return BinaryOp(nodes[0], 'shl', nodes[1])
    def shr(self, *args):
        nodes = [a for a in args if not isinstance(a, Token)]
        return BinaryOp(nodes[0], 'shr', nodes[1])
    def bitnot(self, operand):       return UnaryOp('~', operand)

    # Context blocks -> ContextBlock
    # CTX_*_OPEN and RBRACK are named terminals, producing Token objects
    def ctx_num(self, *args):
        body = [a for a in args if not isinstance(a, Token)]
        return ContextBlock('num', body[0])
    def ctx_bit(self, *args):
        body = [a for a in args if not isinstance(a, Token)]
        return ContextBlock('bit', body[0])
    def ctx_bool(self, *args):
        body = [a for a in args if not isinstance(a, Token)]
        return ContextBlock('bool', body[0])

    # Arithmetic operators -> BinaryOp
    def add(self, left, right):      return BinaryOp(left, '+', right)
    def sub(self, left, right):      return BinaryOp(left, '-', right)
    def mul(self, left, right):      return BinaryOp(left, '*', right)
    def div(self, left, right):      return BinaryOp(left, '/', right)
    def floordiv(self, left, right): return BinaryOp(left, '//', right)
    def mod_op(self, left, right):   return BinaryOp(left, '%', right)
    def power(self, *args):
        nodes = [a for a in args if not isinstance(a, Token)]
        return BinaryOp(nodes[0], '**', nodes[1])

    # Unary operators -> UnaryOp
    def neg(self, operand):          return UnaryOp('-', operand)
    def pos(self, operand):          return UnaryOp('+', operand)

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
# Contextual Lexer (Issue #52: ^ precedence in bit[] context)
# =============================================================================

class CaretPostLex:
    """Post-lexer that transforms ^ tokens based on context block nesting.

    The contextual lexer won't try to match CARET unless it's expected by the
    parser. Since grammar rules reference only CARET_AS_POWER and CARET_AS_XOR
    (declared virtual tokens), CARET is never expected. The always_accept set
    forces the contextual lexer to always match CARET, and this post-lexer
    transforms it into the correct virtual token based on context.

    Context stack tracks bit[...]/num[...]/bool[...] nesting:
    - Default context is 'num' (^ = power at level 12)
    - Inside bit[...], ^ becomes XOR at level 6
    """
    # Tell the contextual lexer to always try matching CARET
    always_accept = frozenset({'CARET'})

    def __init__(self):
        self._stack: List[str] = ['num']

    def reset(self):
        """Reset context stack for a new parse run."""
        self._stack = ['num']

    def process(self, stream):
        """Transform CARET tokens based on context block nesting."""
        for token in stream:
            if token.type == 'CTX_BIT_OPEN':
                self._stack.append('bit')
            elif token.type == 'CTX_NUM_OPEN':
                self._stack.append('num')
            elif token.type == 'CTX_BOOL_OPEN':
                self._stack.append('bool')
            elif token.type == 'RBRACK':
                if len(self._stack) > 1:
                    self._stack.pop()
            elif token.type == 'CARET':
                if self._stack[-1] == 'bit':
                    token.type = 'CARET_AS_XOR'
                else:
                    token.type = 'CARET_AS_POWER'
            yield token


# =============================================================================
# Expression Parser
# =============================================================================

class ExpressionParser:
    """
    Parser for mathematical query expressions.

    Uses Lark to parse expressions into an AST of dataclasses.
    Parse once, evaluate many times. Uses contextual lexing so that
    ^ is parsed at the correct precedence level based on context
    (power in num/default, XOR in bit[...]).

    Example:
        parser = ExpressionParser()
        ast = parser.parse("does_exist primesum(n,2) == 666")
    """

    def __init__(self):
        self._postlex = CaretPostLex()
        self._parser = Lark(
            GRAMMAR,
            parser='lalr',
            transformer=ASTTransformer(),
            postlex=self._postlex,
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

        self._postlex.reset()
        try:
            return self._parser.parse(text)
        except (UnexpectedInput, UnexpectedCharacters, UnexpectedToken) as e:
            raise ParseError(_format_parse_error(e, text), original=e)
        except Exception as e:
            raise ParseError(f"Parse error: {str(e)}", original=e)


# =============================================================================
# Expression Validation ("Compile" Phase)
# =============================================================================

def validate_expression(expr: ASTNode, registry: FunctionRegistry) -> List[str]:
    """
    Validate an expression AST before evaluation.

    Checks for unknown functions and argument count mismatches.
    Run this after parsing but before evaluation to catch errors early.

    Args:
        expr: Parsed AST node
        registry: Function registry to validate against

    Returns:
        List of error messages (empty if valid)
    """
    errors: List[str] = []
    _walk_validate(expr, registry, errors)
    return errors


def _walk_validate(node: ASTNode, registry: FunctionRegistry, errors: List[str]) -> None:
    """Recursively walk AST and collect validation errors."""
    if isinstance(node, FunctionCall):
        # Check function exists
        if node.name not in registry:
            errors.append(f"Unknown function: '{node.name}'")
        else:
            # Check arity
            err = registry.get_validation_error(node.name, len(node.args))
            if err:
                errors.append(err)
        # Validate arguments recursively
        for arg in node.args:
            _walk_validate(arg, registry, errors)
    elif isinstance(node, BinaryOp):
        _walk_validate(node.left, registry, errors)
        _walk_validate(node.right, registry, errors)
    elif isinstance(node, UnaryOp):
        _walk_validate(node.operand, registry, errors)
    elif isinstance(node, Comparison):
        for operand in node.operands:
            _walk_validate(operand, registry, errors)
    elif isinstance(node, ContextBlock):
        _walk_validate(node.body, registry, errors)
    elif isinstance(node, Expression):
        _walk_validate(node.body, registry, errors)


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
    elif isinstance(node, BinaryOp):
        return find_free_variables(node.left) | find_free_variables(node.right)
    elif isinstance(node, UnaryOp):
        return find_free_variables(node.operand)
    elif isinstance(node, Comparison):
        result: Set[str] = set()
        for operand in node.operands:
            result |= find_free_variables(operand)
        return result
    elif isinstance(node, ContextBlock):
        return find_free_variables(node.body)
    elif isinstance(node, Expression):
        return find_free_variables(node.body)
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
        result = evaluator.evaluate(ast.body, {'n': 7})
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

        elif isinstance(node, BinaryOp):
            # Short-circuit: and/or must not eagerly evaluate both sides
            if node.operator in ('and', 'or'):
                ctx = getattr(self, '_eval_context', 'num')
                if ctx == 'bit':
                    # Bitwise: eager evaluate, integer ops
                    left = self.evaluate(node.left, context)
                    right = self.evaluate(node.right, context)
                    if node.operator == 'and':
                        return op_module.and_(int(left), int(right))
                    else:
                        return op_module.or_(int(left), int(right))
                else:
                    # Logical: short-circuit
                    left = self.evaluate(node.left, context)
                    if node.operator == 'and':
                        return self.evaluate(node.right, context) if left else left
                    else:  # or
                        return left if left else self.evaluate(node.right, context)
            # Normal eager evaluation for all other operators
            left = self.evaluate(node.left, context)
            right = self.evaluate(node.right, context)
            return self._binary_op(left, node.operator, right)

        elif isinstance(node, UnaryOp):
            operand = self.evaluate(node.operand, context)
            return self._unary_op(node.operator, operand)

        elif isinstance(node, Comparison):
            # Chained comparisons: a op1 b op2 c → (a op1 b) and (b op2 c)
            # Each operand evaluated exactly once
            values = [self.evaluate(node.operands[0], context)]
            for i, op in enumerate(node.operators):
                next_val = self.evaluate(node.operands[i + 1], context)
                if not self._compare(values[-1], op, next_val):
                    return False
                values.append(next_val)
            return True

        elif isinstance(node, ContextBlock):
            old_context = getattr(self, '_eval_context', 'num')
            self._eval_context = node.context
            try:
                result = self.evaluate(node.body, context)
            finally:
                self._eval_context = old_context
            return result

        elif isinstance(node, Expression):
            return self.evaluate(node.body, context)

        else:
            raise EvaluationError(f"Unknown AST node type: {type(node).__name__}")

    _BINARY_OPS = {
        # Arithmetic
        '+': op_module.add,
        '-': op_module.sub,
        '*': op_module.mul,
        '/': op_module.truediv,
        '//': op_module.floordiv,
        '%': op_module.mod,
        '**': op_module.pow,
        # Bitwise
        'bor': op_module.or_,
        'xor': op_module.xor,
        'band': op_module.and_,
        'shl': op_module.lshift,
        'shr': op_module.rshift,
    }

    _UNARY_OPS = {
        '-': op_module.neg,
        '+': op_module.pos,
        '~': op_module.invert,
        'not': lambda x: not x,
    }

    def _binary_op(self, left: Any, op: str, right: Any) -> Any:
        """Perform a binary operation (arithmetic or bitwise).

        Note: ^ disambiguation is handled at parse time via contextual lexing
        (Issue #52). In bit[] context, ^ parses as XOR at level 6 producing
        BinaryOp('xor'). In num/default context, ^ parses as power at level 12
        producing BinaryOp('**'). ** is always power regardless of context.
        """
        if op in ('/', '//', '%') and right == 0:
            raise EvaluationError(f"Division by zero: {left} {op} {right}")
        try:
            return self._BINARY_OPS[op](left, right)
        except (OverflowError, ValueError) as e:
            raise EvaluationError(f"Arithmetic error: {left} {op} {right} -- {e}")

    def _unary_op(self, op: str, operand: Any) -> Any:
        """Perform a unary operation."""
        # Context-dependent: not means logical NOT in num/default, bitwise NOT in bit
        if op == 'not':
            ctx = getattr(self, '_eval_context', 'num')
            if ctx == 'bit':
                return op_module.invert(int(operand))
            else:
                return not operand
        return self._UNARY_OPS[op](operand)

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
                f"Use 'does_exist' or 'for_any' prefix, e.g.: does_exist {expr.body}"
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
        result = evaluator.evaluate(expr.body, {})
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
        if evaluator.evaluate(expr.body, {}):
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
            if evaluator.evaluate(expr.body, context):
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
    return bool(evaluator.evaluate(expr.body, {}))
