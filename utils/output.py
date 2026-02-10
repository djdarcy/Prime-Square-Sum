"""
Output management library for verbosity, hints, and progress reporting.

This module provides reusable infrastructure — it contains no domain-specific
knowledge about expressions, quantifiers, or bounds. Domain modules register
their own hints at import time via register_hint()/register_hints().

Architecture:
    OutputManager  — central coordinator (verbosity gating, hint dedup, stderr routing)
    Hint           — templatized hint content with context and level metadata
    register_hint  — global registry for hint content (modules self-register)
    init_output    — singleton initialization at program startup
    get_output     — access the singleton from anywhere

Verbosity levels:
    0  (default)  Errors and result-context hints only
    1  (-v)       Progress, timing, summary info
    2  (-vv)      Configuration, algorithm selection, iteration detail
    3  (-vvv)     Internal state, evaluation trace, debug info

Channels (for future filtering, tracked from day one):
    'config'      Configuration loading and overrides
    'parse'       Expression parsing
    'eval'        Expression evaluation
    'iter'        Iteration / search space
    'progress'    Progress counters
    'timing'      Timing information
    'algorithm'   Algorithm selection
    'hint'        Hint messages (auto-assigned)

All non-error output goes to stderr so it never corrupts stdout data streams.

Issue refs: #31 (multi-level verbosity), #53 (quantifier UX hints),
            #57 (structured hint system)
"""

import sys
from dataclasses import dataclass, field
from typing import Any, Dict, Optional, Set, TextIO


# =============================================================================
# Hint registry
# =============================================================================

@dataclass
class Hint:
    """A templatized hint that can be shown in specific contexts.

    Modules create Hint instances and register them via register_hint().
    The OutputManager.hint() method handles context filtering, verbosity
    gating, and session deduplication.

    Attributes:
        id: Unique dot-namespaced identifier (e.g., 'quantifier.use_for_any')
        message: Template string with {var} placeholders for str.format()
        context: Set of contexts where this hint applies:
            'error'   - shown alongside error messages
            'result'  - shown after successful results
            'verbose' - shown only when verbosity >= min_level
        min_level: Minimum verbosity level for 'verbose' context display
        category: Grouping key for channel filtering (e.g., 'quantifier', 'bounds')
    """
    id: str
    message: str
    context: Set[str] = field(default_factory=lambda: {'verbose'})
    min_level: int = 1
    category: str = 'general'


# Global hint registry — populated by modules at import time
_HINTS: Dict[str, Hint] = {}


def register_hint(hint: Hint) -> None:
    """Register a hint in the global registry.

    Typically called at module level so hints are available as soon as
    the module is imported. Duplicate IDs overwrite silently (allows
    reloading during development).
    """
    _HINTS[hint.id] = hint


def register_hints(*hints: Hint) -> None:
    """Register multiple hints at once."""
    for h in hints:
        register_hint(h)


def get_hint(hint_id: str) -> Optional[Hint]:
    """Look up a hint by ID. Returns None if not found."""
    return _HINTS.get(hint_id)


def get_hints_by_category(category: str) -> list:
    """Get all registered hints in a category."""
    return [h for h in _HINTS.values() if h.category == category]


# =============================================================================
# OutputManager
# =============================================================================

class OutputManager:
    """Central coordinator for verbosity-gated output, hints, and progress.

    All output is written to the configured file handle (default: stderr).
    The manager tracks which hints have been shown to avoid repetition
    within a single session.

    This class is domain-agnostic — it doesn't know about expressions,
    quantifiers, or bounds. It provides generic emit/hint/error primitives
    that domain code calls with appropriate parameters.

    Usage::

        out = OutputManager(verbosity=1)
        out.emit(1, "Loaded {count} items", channel='config', count=42)
        out.hint('module.some_hint', 'result', var="value")
        out.progress(100, 3.2)
    """

    def __init__(
        self,
        verbosity: int = 0,
        quiet: bool = False,
        file: TextIO = None,
    ):
        self.verbosity = verbosity
        self.quiet = quiet
        self.file = file if file is not None else sys.stderr
        self._shown_hints: Set[str] = set()

    def emit(self, level: int, message: str, *,
             channel: str = 'general', **kwargs: Any) -> None:
        """Emit a message if verbosity >= level and not quiet.

        Args:
            level: Minimum verbosity level to display this message
            message: Format string (uses str.format with kwargs)
            channel: Output channel name (tracked for future filtering)
            **kwargs: Values for template placeholders
        """
        if self.quiet or self.verbosity < level:
            return
        text = message.format(**kwargs) if kwargs else message
        print(text, file=self.file)

    def hint(self, hint_id: str, context: str = 'result', **kwargs: Any) -> None:
        """Show a hint if appropriate for context, verbosity, and not yet shown.

        Args:
            hint_id: Registry key for the hint
            context: Current context ('error', 'result', 'verbose')
            **kwargs: Values for template placeholders in hint message
        """
        if self.quiet:
            return
        if hint_id in self._shown_hints:
            return
        h = _HINTS.get(hint_id)
        if h is None:
            return
        if context not in h.context:
            return
        if context == 'verbose' and self.verbosity < h.min_level:
            return
        text = h.message.format(**kwargs) if kwargs else h.message
        print(text, file=self.file)
        self._shown_hints.add(hint_id)

    def progress(self, count: int, elapsed: float) -> None:
        """Emit a progress update (requires verbosity >= 1)."""
        self.emit(1, "  ... {count} results ({elapsed:.1f}s)",
                  channel='progress', count=count, elapsed=elapsed)

    def error(self, message: str) -> None:
        """Emit an error message (always shown, even with --quiet)."""
        print(message, file=self.file)

    @property
    def shown_hints(self) -> Set[str]:
        """Set of hint IDs that have been displayed this session."""
        return self._shown_hints.copy()


# =============================================================================
# Module-level singleton
# =============================================================================

_manager: Optional[OutputManager] = None


def init_output(verbosity: int = 0, quiet: bool = False) -> OutputManager:
    """Initialize the module-level OutputManager singleton.

    Call once at program startup after parsing CLI arguments.

    Args:
        verbosity: Verbosity level (0=default, 1=-v, 2=-vv, 3=-vvv)
        quiet: If True, suppress all non-error output

    Returns:
        The initialized OutputManager instance
    """
    global _manager
    _manager = OutputManager(verbosity=verbosity, quiet=quiet)
    return _manager


def get_output() -> OutputManager:
    """Get the module-level OutputManager, creating a default if needed."""
    global _manager
    if _manager is None:
        _manager = OutputManager()
    return _manager
