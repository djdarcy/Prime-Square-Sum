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
