#!/usr/bin/env python3
"""
prime-square-sum.py - Mathematical Expression Evaluator
========================================================

Evaluates mathematical expressions involving prime sums, triangular numbers,
and other sequences to test conjectures and explore relationships.

Core conjecture: stf(10) = 666 = 2² + 3² + 5² + 7² + 11² + 13² + 17²

Usage:
    # Full expression (most flexible)
    python prime-square-sum.py --expr "does_exist primesum(n,2) == 666"

    # Decomposed flags (convenient shortcuts)
    python prime-square-sum.py --target 666
    python prime-square-sum.py --lhs "primesum(n,3)" --target 666

    # Quick verification
    python prime-square-sum.py --verify 666

    # List available functions
    python prime-square-sum.py --list-functions

Author: D. Darcy
Project: https://github.com/djdarcy/Prime-Square-Sum
Related: Zero_AG to The Scarcity Framework (Way-of-Scarcity/papers)
"""

import argparse
import sys
import time
from pathlib import Path

# Version
VERSION_FILE = Path(__file__).parent / "VERSION"
__version__ = VERSION_FILE.read_text().strip() if VERSION_FILE.exists() else "0.7.2"

# Local imports
from utils.grammar import (
    ExpressionParser,
    ExpressionEvaluator,
    ParseError,
    EvaluationError,
    find_free_variables,
    find_matches,
)
from utils.function_registry import FunctionRegistry
from utils.cli import (
    build_expression_from_args,
    build_bounds_from_args,
    list_equations,
    format_match,
    format_no_match,
)
from utils.sieve import generate_n_primes, PRIMESIEVE_AVAILABLE
from utils import gpu as gpu_utils


# =============================================================================
# Argument Parser
# =============================================================================

def create_parser():
    """Create argument parser with all CLI options."""
    parser = argparse.ArgumentParser(
        description='Mathematical expression evaluator for prime sequences',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Find n where sum of squared primes equals 666
  %(prog)s --expr "does_exist primesum(n,2) == 666"

  # Same query using shorthand
  %(prog)s --target 666

  # Find where prime sums equal triangular numbers
  %(prog)s --expr "for_any primesum(n,2) == tri(m)" --max-n 100 --max-m 50

  # Use cubed primes instead of squared
  %(prog)s --lhs "primesum(n,3)" --target 666

  # Quick verification of known result
  %(prog)s --verify 666

  # List all available mathematical functions
  %(prog)s --list-functions

Quantifiers:
  does_exist  Find first match and stop (default)
  for_any     Find all matches within bounds

Comparison operators: ==, !=, <, >, <=, >=
        """
    )

    # === Tier 1: Full Expression ===
    parser.add_argument(
        '--expr', '-e',
        metavar='EXPRESSION',
        help='Full expression (e.g., "does_exist primesum(n,2) == 666")'
    )

    # === Tier 2: Decomposed Flags ===
    parser.add_argument(
        '--lhs',
        metavar='EXPR',
        help='Left-hand side expression (default: primesum(n,2))'
    )
    parser.add_argument(
        '--rhs', '--target', '-t',
        dest='rhs',
        metavar='VALUE',
        help='Right-hand side value (required unless using --expr)'
    )
    parser.add_argument(
        '--operator', '--op',
        metavar='OP',
        choices=['==', '!=', '<', '>', '<=', '>='],
        help='Comparison operator (default: ==)'
    )
    parser.add_argument(
        '--quantifier', '-q',
        metavar='Q',
        choices=['does_exist', 'for_any'],
        help='Quantifier (default: does_exist)'
    )

    # === Tier 3: Saved Equations (Stub for #21) ===
    parser.add_argument(
        '--equation',
        metavar='ID',
        help='Load saved equation by ID or name (v0.7.3+)'
    )
    parser.add_argument(
        '--list-equations',
        action='store_true',
        help='List available saved equations (v0.7.3+)'
    )

    # === Variable Bounds ===
    parser.add_argument(
        '--max-n',
        type=int,
        default=1000000,
        metavar='N',
        help='Maximum value for variable n (default: 1000000)'
    )
    parser.add_argument(
        '--max-m',
        type=int,
        default=10000,
        metavar='M',
        help='Maximum value for variable m (default: 10000)'
    )

    # === Output Control ===
    parser.add_argument(
        '--format', '-f',
        choices=['text', 'json', 'csv'],
        default='text',
        help='Output format (default: text)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed progress and timing'
    )

    # === Convenience Commands ===
    parser.add_argument(
        '--verify',
        metavar='VALUE',
        help='Quick verification (e.g., --verify 666)'
    )
    parser.add_argument(
        '--list-functions',
        action='store_true',
        help='List all available mathematical functions'
    )

    # === Function Loading ===
    parser.add_argument(
        '--functions',
        type=Path,
        action='append',
        metavar='FILE',
        help='Load user-defined functions from Python file'
    )

    # === GPU Control ===
    parser.add_argument(
        '--no-gpu',
        action='store_true',
        help='Disable GPU acceleration'
    )

    # === Version ===
    parser.add_argument(
        '--version',
        action='version',
        version=f'%(prog)s {__version__}'
    )

    return parser


# =============================================================================
# Command Handlers
# =============================================================================

def verify_666(use_gpu: bool = True) -> bool:
    """Quick verification that sum of first 7 squared primes = 666."""
    print("Verifying: stf(10) = 666 = sum of first 7 squared primes")
    print()

    primes = generate_n_primes(7)
    print(f"First 7 primes: {primes.tolist()}")

    if use_gpu and gpu_utils.GPU_AVAILABLE:
        total = gpu_utils.power_sum(primes, power=2, use_gpu=True)
        print(f"Sum (GPU): {total}")
    else:
        squares = [int(p)**2 for p in primes]
        print(f"Squares: {squares}")
        total = sum(squares)
        print(f"Sum: {' + '.join(map(str, squares))} = {total}")

    print()

    if total == 666:
        print("VERIFIED: stf(10) = 666")
        return True
    else:
        print(f"FAILED: Expected 666, got {total}")
        return False


def handle_list_functions(registry: FunctionRegistry) -> int:
    """List all available functions."""
    print("\nAvailable Functions:")
    print("=" * 60)
    for name, description in registry.list_signatures().items():
        print(f"  {description}")
    print("=" * 60)
    print(f"\nTotal: {len(registry)} functions")
    return 0


def handle_expression(args, registry: FunctionRegistry) -> int:
    """Handle expression evaluation."""
    start_time = time.time()

    # Build expression string
    try:
        expr_str = build_expression_from_args(args)
    except (ValueError, NotImplementedError) as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    if args.verbose:
        print(f"Expression: {expr_str}")
        print()

    # Parse expression
    parser = ExpressionParser()
    try:
        ast = parser.parse(expr_str)
    except ParseError as e:
        print(f"Parse error: {e}", file=sys.stderr)
        return 1

    # Create evaluator
    evaluator = ExpressionEvaluator(registry)

    # Build bounds
    bounds = build_bounds_from_args(args, expr_str)

    # Check which variables need bounds
    free_vars = find_free_variables(ast)
    if args.verbose and free_vars:
        print(f"Variables: {', '.join(sorted(free_vars))}")
        print(f"Bounds: {', '.join(f'{k}={v}' for k, v in sorted(bounds.items()) if k in free_vars)}")
        print()

    # Execute
    found_any = False
    match_count = 0

    try:
        for match in find_matches(ast, evaluator, bounds):
            found_any = True
            match_count += 1
            print(format_match(match, args.format))

            # does_exist stops after first match (handled in find_matches)
            # for_any continues

            if args.verbose and match_count % 100 == 0:
                elapsed = time.time() - start_time
                print(f"  ... {match_count} matches found ({elapsed:.1f}s)", file=sys.stderr)

    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except EvaluationError as e:
        print(f"Evaluation error: {e}", file=sys.stderr)
        return 1

    # Summary
    elapsed = time.time() - start_time

    if not found_any:
        print(format_no_match(args.format))

    if args.verbose:
        print()
        print(f"Matches: {match_count}")
        print(f"Time: {elapsed:.2f}s")

    return 0 if found_any else 1


# =============================================================================
# Main Entry Point
# =============================================================================

def main():
    parser = create_parser()
    args = parser.parse_args()

    # Initialize GPU (if not disabled)
    if not args.no_gpu:
        gpu_utils.init_gpu()

    # Load function registry
    registry = FunctionRegistry()

    # Load user functions if specified
    if args.functions:
        for func_file in args.functions:
            if not func_file.exists():
                print(f"Warning: Function file not found: {func_file}", file=sys.stderr)
                continue
            try:
                count = registry.load_from_file(str(func_file))
                if args.verbose:
                    print(f"Loaded {count} function(s) from {func_file}")
            except Exception as e:
                print(f"Error loading {func_file}: {e}", file=sys.stderr)

    # === Handle Special Modes ===

    # List functions
    if args.list_functions:
        return handle_list_functions(registry)

    # List equations (stub for #21)
    if args.list_equations:
        list_equations()
        return 0

    # Verify mode
    if args.verify:
        target = int(args.verify)
        if target == 666:
            success = verify_666(use_gpu=not args.no_gpu)
            return 0 if success else 1
        else:
            # For other values, run as expression
            args.expr = f"does_exist primesum(n,2) == {target}"
            args.rhs = None  # Clear to avoid conflict

    # === Main Expression Evaluation ===

    # Check that we have something to evaluate
    if not args.expr and not args.equation and not args.rhs:
        parser.error(
            "One of the following is required:\n"
            "  --expr EXPRESSION    Full expression\n"
            "  --target VALUE       Right-hand side value (uses default LHS)\n"
            "  --equation ID        Saved equation (v0.7.3+)\n"
            "\n"
            "Examples:\n"
            "  --expr \"does_exist primesum(n,2) == 666\"\n"
            "  --target 666\n"
            "  --lhs \"primesum(n,3)\" --target 666"
        )

    return handle_expression(args, registry)


if __name__ == "__main__":
    sys.exit(main())
