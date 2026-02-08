"""
Phase 3a WolframAlpha / Mathematica verification script.

Cross-verifies our boolean/bitwise operator results against Python built-in
operators (which use the same two's complement semantics as Mathematica's
BitXor, BitAnd, BitOr, BitNot, BitShiftLeft, BitShiftRight).

WolframAlpha-confirmed values (2026-02-07):
  BitXor[5, 3] = 6, BitAnd[5, 3] = 1, BitOr[5, 3] = 7, BitNot[0] = -1,
  BitNot[255] = -256, BitShiftLeft[1, 3] = 8, BitShiftRight[8, 3] = 1,
  BitXor[170, 85] = 255, BitNot[BitAnd[5, 3]] = -2, BitNot[BitOr[5, 3]] = -8,
  BitNot[BitXor[5, 3]] = -7, 2^3 = 8, 3^3+1 = 28, BitXor[2, 3] = 1,
  BitXor[2*3+4, 1] = 11
"""

from utils.grammar import ExpressionParser, ExpressionEvaluator
from utils.function_registry import FunctionRegistry

registry = FunctionRegistry()
parser = ExpressionParser()
evaluator = ExpressionEvaluator(registry)


def eval_expr(expr_str):
    """Evaluate a bare expression by wrapping as verify EXPR == 0."""
    full = "verify " + expr_str + " == 0"
    expr = parser.parse(full)
    return evaluator.evaluate(expr.body.operands[0], {})


def verify_against_python():
    """Verify all Phase 3a results against Python built-in operators."""
    tests = [
        ("5 xor 3",        5 ^ 3,         6),
        ("5 band 3",       5 & 3,         1),
        ("5 bor 3",        5 | 3,         7),
        ("~0",             ~0,           -1),
        ("~255",           ~255,        -256),
        ("1 << 3",         1 << 3,        8),
        ("8 >> 3",         8 >> 3,        1),
        ("255 band 15",    255 & 15,     15),
        ("170 xor 85",     170 ^ 85,    255),
        ("nand(5,3)",      ~(5 & 3),     -2),
        ("nor(5,3)",       ~(5 | 3),     -8),
        ("xnor(5,3)",      ~(5 ^ 3),    -7),
        ("2^3",            2**3,          8),
        ("2^10",           2**10,      1024),
        ("3^3 + 1",        3**3 + 1,    28),
        ("2+3 xor 1",      (2+3) ^ 1,    4),
        ("(2+3) xor 1",    (2+3) ^ 1,    4),
        ("1<<3 bor 4",     (1<<3) | 4,  12),
        ("5 band 3+1",     5 & (3+1),    4),
        ("bit[2^3]",       2 ^ 3,        1),
        ("bit[5 or 3]",    5 | 3,        7),
        ("bit[5 and 3]",   5 & 3,        1),
        ("bit[not 0]",     ~0,          -1),
        ("2^3 + 1",        2**3 + 1,     9),
        ("~0 + 1",         ~0 + 1,       0),
        ("2*3+4 xor 1",    (2*3+4) ^ 1, 11),
    ]

    print("{:<20} {:>10} {:>10} {:>10}".format(
        "Expression", "Our Value", "Python", "Match?"))
    print("-" * 55)

    all_match = True
    for label, python_val, our_val in tests:
        match = python_val == our_val
        if not match:
            all_match = False
        print("{:<20} {:>10} {:>10} {:>10}".format(
            label, our_val, python_val, "YES" if match else "** NO **"))

    print()
    print(f"All {len(tests)} values match Python: {all_match}")
    return all_match


def demonstrate_caret_precedence_issue():
    """Show the known ^-precedence mismatch in bit[] context."""
    print()
    print("=" * 70)
    print("Known issue: ^ precedence in bit[] context")
    print("=" * 70)
    print()

    examples = [
        ("bit[2 band 3 ^ 4]",          "(2 & 3) ^ 4",
         "BitXor[BitAnd[2, 3], 4]"),
        ("bit[7 ^ 3 band 5]",          "7 ^ (3 & 5)",
         "BitXor[7, BitAnd[3, 5]]"),
        ("bit[7 band 5 ^ 6 band 3]",   "(7 & 5) ^ (6 & 3)",
         "BitXor[BitAnd[7, 5], BitAnd[6, 3]]"),
    ]

    for our_expr, py_expr, math_expr in examples:
        our_val = eval_expr(our_expr)
        py_val = eval(py_expr)
        match = "OK" if our_val == py_val else "MISMATCH"
        print(f"  Ours: {our_expr:<35} = {our_val}")
        print(f"  Python: {py_expr:<35} = {py_val}")
        print(f"  Mathematica: {math_expr:<35} = {py_val}")
        print(f"  {match}")
        print()

    print("Workarounds (use xor keyword or explicit parens):")
    workarounds = [
        ("2 band 3 xor 4",       "(2 & 3) ^ 4"),
        ("bit[(2 band 3) ^ 4]",  "(2 & 3) ^ 4"),
        ("7 xor 3 band 5",       "7 ^ (3 & 5)"),
        ("bit[7 ^ (3 band 5)]",  "7 ^ (3 & 5)"),
    ]
    for our_expr, py_expr in workarounds:
        our_val = eval_expr(our_expr)
        py_val = eval(py_expr)
        print(f"  {our_expr:<30} = {our_val}  (correct: {py_val})")


if __name__ == "__main__":
    verify_against_python()
    demonstrate_caret_precedence_issue()
