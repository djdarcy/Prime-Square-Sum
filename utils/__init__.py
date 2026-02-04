"""
Prime-Square-Sum Utilities
==========================

Optimized utilities for prime generation, loading, and computation.
"""

from .prime_io import load_primes, save_primes, load_primes_range
from .sieve import generate_primes, nth_prime, prime_count
from .gpu import init_gpu, gpu_power_sum, cpu_power_sum, power_sum, GPU_AVAILABLE
from .function_registry import FunctionRegistry, FunctionSignature
from .sequences import primesum, fibonacci, factorial, catalan
from .grammar import (
    # AST classes
    Expression,
    Comparison,
    FunctionCall,
    Variable,
    Literal,
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
from .cli import (
    # Expression building
    ExpressionComponents,
    build_expression_from_args,
    build_bounds_from_args,
    format_match,
    format_no_match,
    # Equation loading (Issue #21)
    SavedEquation,
    EquationsFile,
    ParameterDef,
    load_equations_file,
    find_equations_file,
    list_equations,
    print_equations_list,
    parse_var_string,
    # Configuration (Issue #22)
    Config,
    load_config,
    find_config_file,
    resolve_default_equation,
    show_config,
)

__all__ = [
    # Prime I/O
    'load_primes',
    'save_primes',
    'load_primes_range',
    # Prime generation
    'generate_primes',
    'nth_prime',
    'prime_count',
    # GPU computation
    'init_gpu',
    'gpu_power_sum',
    'cpu_power_sum',
    'power_sum',
    'GPU_AVAILABLE',
    # Function registry
    'FunctionRegistry',
    'FunctionSignature',
    # Sequences
    'primesum',
    'fibonacci',
    'factorial',
    'catalan',
    # Expression grammar (Issue #17)
    'Expression',
    'Comparison',
    'FunctionCall',
    'Variable',
    'Literal',
    'ExpressionParser',
    'ParseError',
    'ExpressionEvaluator',
    'EvaluationError',
    'find_free_variables',
    'find_matches',
]
