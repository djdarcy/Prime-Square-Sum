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
    format_match,
    format_no_match,
    # Issue #21: Equation loading
    print_equations_list,
    load_equations_file,
    # Issue #22: Configuration
    load_config,
    show_config,
)
from utils.sieve import (
    generate_n_primes, PRIMESIEVE_AVAILABLE,
    get_available_algorithms, get_algorithm_info, configure as configure_sieve,
    ALGORITHM_AUTO, ALGORITHM_PRIMESIEVE, ALGORITHM_BASIC,
    ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL,
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

  # List all available mathematical functions
  %(prog)s --list-functions

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
        '--list-equations',
        action='store_true',
        help='List available saved equations'
    )
    parser.add_argument(
        '--var',
        action='append',
        metavar='NAME=VALUE',
        help='Set equation parameter (e.g., --var a=3 or --var a=3,b=4)'
    )
    parser.add_argument(
        '--show-config',
        action='store_true',
        help='Show effective configuration and default equation'
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
    parser.add_argument(
        '--list-algorithms',
        action='store_true',
        help='List available algorithm variants'
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

def handle_list_functions(registry: FunctionRegistry) -> int:
    """List all available functions."""
    print("\nAvailable Functions:")
    print("=" * 60)
    for name, description in registry.list_signatures().items():
        print(f"  {description}")
    print("=" * 60)
    print(f"\nTotal: {len(registry)} functions")
    return 0


def handle_list_algorithms() -> int:
    """List all available algorithm variants."""
    print("\nAvailable Algorithm Variants:")
    print("=" * 60)

    info = get_algorithm_info()
    available = get_available_algorithms()

    # Group by class (currently only sieve)
    print("\nSieve Algorithms (--algorithm sieve:<variant>):")
    print("-" * 50)

    for algo in [ALGORITHM_AUTO, ALGORITHM_PRIMESIEVE, ALGORITHM_BASIC,
                 ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
        algo_info = info.get(algo, {})
        status = "OK" if algo_info.get("available", False) else "NOT INSTALLED"
        desc = algo_info.get("description", "")
        time_c = algo_info.get("complexity_time", "")
        space_c = algo_info.get("complexity_space", "")

        print(f"  {algo:12} [{status}]")
        print(f"               {desc}")
        if time_c:
            print(f"               Time: {time_c}, Space: {space_c}")
        print()

    print("Usage:")
    print("  --algorithm sieve:auto        Auto-select best available")
    print("  --algorithm sieve:segmented   Force segmented (bounded memory)")
    print("  --algorithm sieve:basic       Force basic sieve")
    print("  --algorithm sieve:individual  Force individual testing")
    print()
    print("Resource preferences (--prefer):")
    print("  cpu      Prefer CPU-intensive algorithms")
    print("  memory   Prefer faster algorithms even if memory-heavy")
    print("  minimal  Prefer minimal memory usage")
    print("  gpu      Prefer GPU acceleration where available")

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

    # List functions
    if args.list_functions:
        return handle_list_functions(registry)

    # List algorithms (Issue #29)
    if args.list_algorithms:
        return handle_list_algorithms()

    # Show config (Issue #22)
    if args.show_config:
        show_config()
        return 0

    # List equations (Issue #21)
    if args.list_equations:
        print_equations_list()
        return 0

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
