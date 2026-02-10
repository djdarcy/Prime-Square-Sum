"""
Domain-specific hint content for Prime-Square-Sum.

Each section registers hints that belong to its domain. The output library
(utils.output) provides the infrastructure; this module provides the content.

Hint ID convention: '{category}.{specific_name}'
    quantifier.*   — directive/quantifier guidance
    bounds.*       — variable bounds and defaults
    iteration.*    — iteration order and search space
    format.*       — output format suggestions

Other modules (e.g., a future sieve hints module) can register their own
hints by importing register_hint/register_hints from utils.output.
"""

from utils.output import Hint, register_hints


# =============================================================================
# Quantifier / directive hints
# =============================================================================

register_hints(
    Hint(
        id='quantifier.use_for_any',
        message='Tip: Use "for_any" to find all matches in the search space.',
        context={'result'},
        min_level=0,
        category='quantifier',
    ),
    Hint(
        id='quantifier.use_solve',
        message='Tip: Use "solve" to compute a value, or "verify" to check truthiness.',
        context={'error'},
        min_level=0,
        category='quantifier',
    ),
    Hint(
        id='quantifier.use_verify',
        message='Tip: Use "verify" for closed expressions (no free variables).',
        context={'error'},
        min_level=0,
        category='quantifier',
    ),
    Hint(
        id='quantifier.solve_enum',
        message='Tip: Use "solve {expr}" with --max-{var} to enumerate values.',
        context={'error'},
        min_level=0,
        category='quantifier',
    ),
    Hint(
        id='quantifier.limit_with_does_exist',
        message='Note: --limit has no effect with does_exist (stops at first match). '
                'Tip: Use "for_any ... --limit N" to find multiple matches.',
        context={'result'},
        min_level=0,
        category='quantifier',
    ),
)


# =============================================================================
# Bounds hints
# =============================================================================

register_hints(
    Hint(
        id='bounds.implicit_defaults',
        message='Note: Using default bounds ({bounds}). Use {flags} to customize.',
        context={'verbose'},
        min_level=1,
        category='bounds',
    ),
)


# =============================================================================
# Iteration hints
# =============================================================================

register_hints(
    Hint(
        id='iteration.cartesian_order',
        message='Note: Variables iterated alphabetically ({order}). '
                'See --iter-var for custom ordering.',
        context={'verbose'},
        min_level=2,
        category='iteration',
    ),
    Hint(
        id='iteration.large_space',
        message='Note: Search space is {size:,} combinations. Use Ctrl+C to interrupt.',
        context={'verbose'},
        min_level=1,
        category='iteration',
    ),
)


# =============================================================================
# Output format hints
# =============================================================================

register_hints(
    Hint(
        id='format.pipe_safe',
        message='Tip: Use --format json or --format csv for machine-readable output.',
        context={'verbose'},
        min_level=2,
        category='format',
    ),
)
