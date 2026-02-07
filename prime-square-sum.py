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

    # Verify known result (no iteration)
    python prime-square-sum.py --expr "verify primesum(7,2) == 666"

    # List available functions, equations, or other resources
    python prime-square-sum.py --list functions

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
    validate_expression,
)
from utils.function_registry import FunctionRegistry
from utils.cli import (
    build_expression_from_args,
    build_bounds_from_args,
    build_iterator_factories_from_args,
    format_match,
    format_no_match,
    # Issue #22: Configuration
    load_config,
)
from utils.list_commands import handle_list
from utils.sieve import (
    generate_n_primes, PRIMESIEVE_AVAILABLE,
    configure as configure_sieve,
)
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

  # Verify known result (no search, returns true/false)
  %(prog)s --expr "verify primesum(7,2) == 666"

  # Implicit verify (auto-detected when no free variables)
  %(prog)s --expr "primesum(7,2) == 666"

  # List available resources
  %(prog)s --list functions
  %(prog)s --list equations
  %(prog)s --list                   # show available categories

Quantifiers:
  does_exist  Find first match and stop (default)
  for_any     Find all matches within bounds
  verify      Evaluate closed formula, return true/false

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

    # === Tier 3: Saved Equations (Issue #21) ===
    parser.add_argument(
        '--equation',
        metavar='ID',
        help='Load saved equation by ID or name'
    )
    parser.add_argument(
        '--var',
        action='append',
        metavar='NAME=VALUE',
        help='Set equation parameter (e.g., --var a=3 or --var a=3,b=4)'
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

    # === Iterator Configuration (Issue #37) ===
    parser.add_argument(
        '--iter-var',
        action='append',
        metavar='VAR:START:STOP[:STEP][:DTYPE]',
        help='Define iterator for variable (e.g., n:1:1000:2:uint64)'
    )
    parser.add_argument(
        '--iter-type',
        action='append',
        metavar='VAR:TYPE',
        help='Set iterator type for variable (int or float)'
    )
    parser.add_argument(
        '--iter-start',
        action='append',
        metavar='VAR:VALUE',
        help='Set iterator start value for variable'
    )
    parser.add_argument(
        '--iter-stop',
        action='append',
        metavar='VAR:VALUE',
        help='Set iterator stop value for variable'
    )
    parser.add_argument(
        '--iter-step',
        action='append',
        metavar='VAR:VALUE',
        help='Set iterator step for variable'
    )
    parser.add_argument(
        '--iter-num-steps',
        action='append',
        metavar='VAR:COUNT',
        help='Set number of steps for float iterator (linspace-style)'
    )
    parser.add_argument(
        '--iter-dtype',
        action='append',
        metavar='VAR:DTYPE',
        help='Set dtype validation (int/int32/int64/uint64/float32/float64)'
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

    # === List / Info Commands ===
    _list_categories = ['functions', 'equations', 'algorithms', 'config', 'all']
    parser.add_argument(
        '--list',
        nargs='?',
        const='menu',
        metavar='{' + ','.join(_list_categories) + '}',
        help='List available resources (functions, equations, algorithms, config, all)'
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

    # === Algorithm Selection (Issue #29) ===
    parser.add_argument(
        '--algorithm',
        metavar='CLASS:VARIANT',
        help='Algorithm selection (e.g., sieve:segmented, sieve:basic, sieve:individual)'
    )
    parser.add_argument(
        '--prefer',
        choices=['cpu', 'gpu', 'memory', 'minimal'],
        help='Resource preference hint for auto-selection'
    )
    parser.add_argument(
        '--max-memory',
        type=int,
        metavar='MB',
        help='Maximum memory usage in MB for sieve operations'
    )

    # === Version ===
    parser.add_argument(
        '--version',
        action='version',
        version=f'%(prog)s {__version__}'
    )

    return parser


# =============================================================================
# Expression Handler
# =============================================================================

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

    # Validate expression (compile phase)
    validation_errors = validate_expression(ast, registry)
    if validation_errors:
        for err in validation_errors:
            print(f"Error: {err}", file=sys.stderr)
        return 1

    # Create evaluator
    evaluator = ExpressionEvaluator(registry)

    # Build bounds
    bounds = build_bounds_from_args(args, expr_str)

    # Build iterator factories (Issue #37)
    iterator_factories = build_iterator_factories_from_args(args, bounds)

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
        for match in find_matches(ast, evaluator, bounds, iterator_factories):
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

def parse_algorithm_arg(algo_str: str) -> tuple:
    """
    Parse --algorithm argument in 'class:variant' format.

    Args:
        algo_str: String like "sieve:segmented"

    Returns:
        Tuple of (class, variant)

    Raises:
        ValueError: If format is invalid
    """
    if ':' not in algo_str:
        raise ValueError(
            f"Invalid algorithm format: {algo_str}\n"
            f"Expected format: class:variant (e.g., sieve:segmented)"
        )

    parts = algo_str.split(':', 1)
    return parts[0].lower(), parts[1].lower()


def main():
    parser = create_parser()
    args = parser.parse_args()

    # Load config for algorithm defaults (Issue #29)
    # Precedence: CLI > config.json > auto-detection
    config = load_config()

    # Apply config.json algorithm settings first (lower precedence)
    if config.algorithms.get('sieve'):
        configure_sieve(algorithm=config.algorithms['sieve'])
        if args.verbose:
            print(f"[INFO] Sieve algorithm (config): {config.algorithms['sieve']}")

    if config.max_memory_mb:
        configure_sieve(max_memory_mb=config.max_memory_mb)
        if args.verbose:
            print(f"[INFO] Max memory (config): {config.max_memory_mb} MB")

    if config.prefer:
        configure_sieve(prefer=config.prefer)
        if args.verbose:
            print(f"[INFO] Resource preference (config): {config.prefer}")

    # Apply CLI flags (higher precedence, overrides config)
    if args.algorithm:
        try:
            algo_class, algo_variant = parse_algorithm_arg(args.algorithm)
            if algo_class == "sieve":
                configure_sieve(algorithm=algo_variant)
                if args.verbose:
                    print(f"[INFO] Sieve algorithm (CLI): {algo_variant}")
            else:
                print(f"Warning: Unknown algorithm class '{algo_class}', ignoring",
                      file=sys.stderr)
        except ValueError as e:
            print(f"Error: {e}", file=sys.stderr)
            return 1

    if args.max_memory:
        configure_sieve(max_memory_mb=args.max_memory)
        if args.verbose:
            print(f"[INFO] Max memory (CLI): {args.max_memory} MB")

    if args.prefer:
        configure_sieve(prefer=args.prefer)
        if args.verbose:
            print(f"[INFO] Resource preference (CLI): {args.prefer}")

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

    # Unified --list dispatch (#47)
    if args.list is not None:
        valid = {'functions', 'equations', 'algorithms', 'config', 'all', 'menu'}
        if args.list not in valid:
            parser.error(
                f"argument --list: invalid choice: '{args.list}' "
                f"(choose from functions, equations, algorithms, config, all)"
            )
        return handle_list(args.list, args, registry)

    # === Main Expression Evaluation ===

    # Check that we have something to evaluate
    if not args.expr and not args.equation and not args.rhs:
        parser.error(
            "One of the following is required:\n"
            "  --expr EXPRESSION    Full expression\n"
            "  --target VALUE       Right-hand side value (uses default equation)\n"
            "  --equation ID        Load saved equation by ID or name\n"
            "\n"
            "Examples:\n"
            "  --expr \"does_exist primesum(n,2) == 666\"\n"
            "  --target 666\n"
            "  --lhs \"primesum(n,3)\" --target 666"
        )

    return handle_expression(args, registry)


if __name__ == "__main__":
    sys.exit(main())
