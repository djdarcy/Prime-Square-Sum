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

from utils.output import init_output, get_output
import utils.hints  # noqa: F401 — registers domain hints at import time

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

Directives/Quantifiers:
  does_exist  Find first match and stop (default)
  for_any     Find all matches within bounds
  verify      Evaluate closed formula, return true/false
  solve       Compute value (calculator) or enumerate sequences

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
        action='count',
        default=0,
        help='Increase verbosity (-v=progress, -vv=detail, -vvv=debug)'
    )
    parser.add_argument(
        '--quiet', '-Q',
        action='store_true',
        help='Suppress all non-error output (hints, progress, timing)'
    )
    parser.add_argument(
        '--limit',
        type=int,
        metavar='N',
        help='Maximum number of results for enumeration (for_any/solve)'
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

def handle_expression(args, registry: FunctionRegistry, config=None) -> int:
    """Handle expression evaluation."""
    out = get_output()
    start_time = time.time()

    # Build expression string
    try:
        expr_str = build_expression_from_args(args)
    except (ValueError, NotImplementedError) as e:
        out.error(f"Error: {e}")
        return 1

    out.emit(1, "Expression: {expr}", channel='parse', expr=expr_str)
    out.emit(1, "", channel='parse')

    # Parse expression (Issue #54, Phase 2: configurable imaginary suffixes)
    imag_patterns = {'ii': '[iI][iI]', 'i': '[iI]', 'j': '[jJ]', 'both': '[iIjJ]', 'none': ''}
    imag_unit = config.imaginary_unit if config else 'none'
    suffix_pattern = imag_patterns.get(imag_unit, '[iI][iI]')
    parser = ExpressionParser(imaginary_suffix_pattern=suffix_pattern)
    try:
        ast = parser.parse(expr_str)
    except ParseError as e:
        out.error(f"Parse error: {e}")
        return 1

    # Validate expression (compile phase)
    validation_errors = validate_expression(ast, registry)
    if validation_errors:
        for err in validation_errors:
            out.error(f"Error: {err}")
        return 1

    # Create evaluator
    evaluator = ExpressionEvaluator(registry)

    # Build bounds
    bounds = build_bounds_from_args(args, expr_str)

    # Build iterator factories (Issue #37)
    iterator_factories = build_iterator_factories_from_args(args, bounds)

    # Check which variables need bounds
    free_vars = find_free_variables(ast)
    if free_vars:
        out.emit(1, "Variables: {vars}", channel='iter', vars=', '.join(sorted(free_vars)))
        bound_info = ', '.join(
            f'{k}={v:,}' for k, v in sorted(bounds.items()) if k in free_vars
        )
        out.emit(1, "Bounds: {bounds}", channel='iter', bounds=bound_info)
        out.emit(1, "", channel='iter')

        # Hint: surface implicit default bounds (#58)
        default_bounds = {
            v: bounds[v] for v in sorted(free_vars)
            if v in bounds and not _has_explicit_bound(args, v)
        }
        if default_bounds:
            bound_str = ', '.join(f'{v}={val:,}' for v, val in default_bounds.items())
            flag_str = ', '.join(f'--max-{v}' for v in default_bounds)
            out.hint('bounds.implicit_defaults', 'verbose',
                     bounds=bound_str, flags=flag_str)

        # Hint: large search space
        if len(free_vars) >= 2:
            space_size = 1
            for v in free_vars:
                space_size *= bounds.get(v, 1)
            out.hint('iteration.large_space', 'verbose', size=space_size)

            # Hint: iteration order
            out.hint('iteration.cartesian_order', 'verbose',
                     order=', '.join(sorted(free_vars)))

    # Execute
    found_any = False
    match_count = 0
    limit = getattr(args, 'limit', None)

    try:
        for match in find_matches(ast, evaluator, bounds, iterator_factories):
            found_any = True
            match_count += 1
            print(format_match(match, args.format))

            # Respect --limit for enumeration modes
            if limit is not None and match_count >= limit:
                break

            # does_exist stops after first match (handled in find_matches)
            # for_any continues

            if match_count % 100 == 0:
                elapsed = time.time() - start_time
                out.progress(match_count, elapsed)

    except KeyboardInterrupt:
        # Graceful interruption — results already printed to stdout are preserved
        elapsed = time.time() - start_time
        out.error(f"\nInterrupted after {match_count} results ({elapsed:.1f}s)")
        return 0 if found_any else 1
    except ValueError as e:
        out.error(f"Error: {e}")
        return 1
    except EvaluationError as e:
        out.error(f"Evaluation error: {e}")
        return 1

    # Summary
    elapsed = time.time() - start_time

    if not found_any:
        print(format_no_match(args.format))

    out.emit(1, "", channel='timing')
    out.emit(1, "Matches: {count}", channel='timing', count=match_count)
    out.emit(1, "Time: {elapsed:.2f}s", channel='timing', elapsed=elapsed)

    # Post-result hints (separated from results by a blank line)
    quantifier = ast.quantifier
    hint_separator_needed = (
        (quantifier == "does_exist" and found_any and len(free_vars) >= 2)
        or (quantifier == "does_exist" and limit is not None)
    )
    if hint_separator_needed and not out.quiet:
        out.emit(0, "", channel='hint')
    if quantifier == "does_exist" and found_any and len(free_vars) >= 2:
        out.hint('quantifier.use_for_any', 'result')
    if quantifier == "does_exist" and limit is not None:
        out.hint('quantifier.limit_with_does_exist', 'result')

    return 0 if found_any else 1


def _has_explicit_bound(args, var_name: str) -> bool:
    """Check if a variable's bound was explicitly set via CLI flags."""
    # Check --max-{var} style flags
    attr = f'max_{var_name}'
    if hasattr(args, attr):
        # argparse sets defaults; check if user provided it
        # Default values: n=1000000, m=10000
        defaults = {'max_n': 1000000, 'max_m': 10000}
        val = getattr(args, attr)
        if attr in defaults and val == defaults[attr]:
            return False  # Still at default
        return True
    # Check --iter-var overrides
    if args.iter_var:
        for spec in args.iter_var:
            if spec.startswith(f'{var_name}:'):
                return True
    return False


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

    # Initialize output manager (#31, #57)
    out = init_output(
        verbosity=args.verbose if not args.quiet else 0,
        quiet=args.quiet,
    )

    # Load config for algorithm defaults (Issue #29)
    # Precedence: CLI > config.json > auto-detection
    config = load_config()

    # Apply config.json algorithm settings first (lower precedence)
    if config.algorithms.get('sieve'):
        configure_sieve(algorithm=config.algorithms['sieve'])
        out.emit(2, "[config] Sieve algorithm: {algo}",
                 channel='config', algo=config.algorithms['sieve'])

    if config.max_memory_mb:
        configure_sieve(max_memory_mb=config.max_memory_mb)
        out.emit(2, "[config] Max memory: {mb} MB",
                 channel='config', mb=config.max_memory_mb)

    if config.prefer:
        configure_sieve(prefer=config.prefer)
        out.emit(2, "[config] Resource preference: {pref}",
                 channel='config', pref=config.prefer)

    # Apply CLI flags (higher precedence, overrides config)
    if args.algorithm:
        try:
            algo_class, algo_variant = parse_algorithm_arg(args.algorithm)
            if algo_class == "sieve":
                configure_sieve(algorithm=algo_variant)
                out.emit(2, "[cli] Sieve algorithm: {algo}",
                         channel='algorithm', algo=algo_variant)
            else:
                out.error(f"Warning: Unknown algorithm class '{algo_class}', ignoring")
        except ValueError as e:
            out.error(f"Error: {e}")
            return 1

    if args.max_memory:
        configure_sieve(max_memory_mb=args.max_memory)
        out.emit(2, "[cli] Max memory: {mb} MB",
                 channel='algorithm', mb=args.max_memory)

    if args.prefer:
        configure_sieve(prefer=args.prefer)
        out.emit(2, "[cli] Resource preference: {pref}",
                 channel='algorithm', pref=args.prefer)

    # Initialize GPU (if not disabled)
    if not args.no_gpu:
        gpu_utils.init_gpu()

    # Load function registry
    registry = FunctionRegistry()

    # Load user functions if specified
    if args.functions:
        for func_file in args.functions:
            if not func_file.exists():
                out.error(f"Warning: Function file not found: {func_file}")
                continue
            try:
                count = registry.load_from_file(str(func_file))
                out.emit(1, "Loaded {count} function(s) from {path}",
                         channel='config', count=count, path=func_file)
            except Exception as e:
                out.error(f"Error loading {func_file}: {e}")

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

    return handle_expression(args, registry, config)


if __name__ == "__main__":
    sys.exit(main())
