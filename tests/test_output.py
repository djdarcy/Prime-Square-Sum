"""
Tests for utils.output (OutputManager, Hint registry) and utils.hints.

Tests the output library independently of the CLI to verify:
- Verbosity level gating
- Hint registration and retrieval
- Context-aware hint display
- Session deduplication
- Quiet mode suppression
- Channel parameter tracking
- Template variable substitution
"""

import io
import pytest

from utils.output import (
    OutputManager,
    Hint,
    register_hint,
    register_hints,
    get_hint,
    get_hints_by_category,
    init_output,
    get_output,
    _HINTS,
)


# =============================================================================
# Fixtures
# =============================================================================

@pytest.fixture
def buf():
    """A StringIO buffer for capturing output."""
    return io.StringIO()


@pytest.fixture
def out(buf):
    """An OutputManager writing to a buffer (verbosity=0)."""
    return OutputManager(verbosity=0, file=buf)


@pytest.fixture
def out_v1(buf):
    """An OutputManager at verbosity level 1."""
    return OutputManager(verbosity=1, file=buf)


@pytest.fixture
def out_v2(buf):
    """An OutputManager at verbosity level 2."""
    return OutputManager(verbosity=2, file=buf)


@pytest.fixture
def out_quiet(buf):
    """An OutputManager in quiet mode."""
    return OutputManager(verbosity=2, quiet=True, file=buf)


# =============================================================================
# OutputManager.emit tests
# =============================================================================

class TestEmit:
    """Test verbosity-gated message emission."""

    def test_emit_level_0_default(self, out, buf):
        """Level 0 messages don't display at default verbosity."""
        # emit(0, ...) does display at verbosity=0
        out.emit(0, "hello")
        assert buf.getvalue() == "hello\n"

    def test_emit_level_1_hidden_at_v0(self, out, buf):
        """Level 1 messages are hidden at verbosity 0."""
        out.emit(1, "hidden")
        assert buf.getvalue() == ""

    def test_emit_level_1_shown_at_v1(self, out_v1, buf):
        """Level 1 messages are shown at verbosity 1."""
        out_v1.emit(1, "visible")
        assert "visible" in buf.getvalue()

    def test_emit_level_2_hidden_at_v1(self, out_v1, buf):
        """Level 2 messages are hidden at verbosity 1."""
        out_v1.emit(2, "hidden")
        assert buf.getvalue() == ""

    def test_emit_level_2_shown_at_v2(self, out_v2, buf):
        """Level 2 messages are shown at verbosity 2."""
        out_v2.emit(2, "detail")
        assert "detail" in buf.getvalue()

    def test_emit_template_substitution(self, out_v1, buf):
        """Template variables are substituted."""
        out_v1.emit(1, "Found {n} at {loc}", n=7, loc="origin")
        assert "Found 7 at origin" in buf.getvalue()

    def test_emit_no_kwargs_no_format(self, out_v1, buf):
        """Messages without kwargs are passed through verbatim."""
        out_v1.emit(1, "plain {message}")
        assert "plain {message}" in buf.getvalue()

    def test_emit_channel_parameter_accepted(self, out_v1, buf):
        """Channel parameter is accepted without error."""
        out_v1.emit(1, "config loaded", channel='config')
        assert "config loaded" in buf.getvalue()


# =============================================================================
# OutputManager.hint tests
# =============================================================================

# Test-local hint for isolation
_TEST_HINT_RESULT = Hint(
    id='_test.result_hint',
    message='Test result hint: {info}',
    context={'result'},
    min_level=0,
    category='test',
)

_TEST_HINT_VERBOSE = Hint(
    id='_test.verbose_hint',
    message='Test verbose hint',
    context={'verbose'},
    min_level=1,
    category='test',
)

_TEST_HINT_ERROR = Hint(
    id='_test.error_hint',
    message='Test error hint',
    context={'error'},
    min_level=0,
    category='test',
)

# Register test hints
register_hints(_TEST_HINT_RESULT, _TEST_HINT_VERBOSE, _TEST_HINT_ERROR)


class TestHint:
    """Test context-aware hint display."""

    def test_hint_shown_in_matching_context(self, out, buf):
        """Hint is shown when context matches."""
        out.hint('_test.result_hint', 'result', info='works')
        assert "Test result hint: works" in buf.getvalue()

    def test_hint_hidden_in_wrong_context(self, out, buf):
        """Hint is hidden when context doesn't match."""
        out.hint('_test.result_hint', 'verbose', info='x')
        assert buf.getvalue() == ""

    def test_hint_verbose_shown_at_level(self, out_v1, buf):
        """Verbose-context hint is shown at sufficient verbosity."""
        out_v1.hint('_test.verbose_hint', 'verbose')
        assert "Test verbose hint" in buf.getvalue()

    def test_hint_verbose_hidden_below_level(self, out, buf):
        """Verbose-context hint is hidden below min_level."""
        out.hint('_test.verbose_hint', 'verbose')
        assert buf.getvalue() == ""

    def test_hint_dedup(self, out, buf):
        """Same hint is not shown twice."""
        out.hint('_test.result_hint', 'result', info='first')
        out.hint('_test.result_hint', 'result', info='second')
        output = buf.getvalue()
        assert output.count("Test result hint") == 1
        assert "first" in output

    def test_hint_dedup_tracked(self, out, buf):
        """Shown hints are tracked."""
        out.hint('_test.result_hint', 'result', info='x')
        assert '_test.result_hint' in out.shown_hints

    def test_hint_unknown_id_ignored(self, out, buf):
        """Unknown hint IDs are silently ignored."""
        out.hint('nonexistent.hint', 'result')
        assert buf.getvalue() == ""

    def test_hint_error_context(self, out, buf):
        """Error-context hints are shown at verbosity 0."""
        out.hint('_test.error_hint', 'error')
        assert "Test error hint" in buf.getvalue()


# =============================================================================
# Quiet mode tests
# =============================================================================

class TestQuietMode:
    """Test --quiet suppression."""

    def test_quiet_suppresses_emit(self, out_quiet, buf):
        """Quiet mode suppresses emit() even at high verbosity."""
        out_quiet.emit(1, "should not appear")
        assert buf.getvalue() == ""

    def test_quiet_suppresses_hints(self, out_quiet, buf):
        """Quiet mode suppresses hints."""
        out_quiet.hint('_test.result_hint', 'result', info='x')
        assert buf.getvalue() == ""

    def test_quiet_allows_errors(self, out_quiet, buf):
        """Quiet mode still allows error() output."""
        out_quiet.error("critical error")
        assert "critical error" in buf.getvalue()

    def test_quiet_allows_progress_suppression(self, out_quiet, buf):
        """Quiet mode suppresses progress."""
        out_quiet.progress(100, 3.5)
        assert buf.getvalue() == ""


# =============================================================================
# Progress tests
# =============================================================================

class TestProgress:
    """Test progress reporting."""

    def test_progress_at_v1(self, out_v1, buf):
        """Progress is shown at verbosity 1."""
        out_v1.progress(100, 3.5)
        output = buf.getvalue()
        assert "100" in output
        assert "3.5s" in output

    def test_progress_hidden_at_v0(self, out, buf):
        """Progress is hidden at verbosity 0."""
        out.progress(100, 3.5)
        assert buf.getvalue() == ""


# =============================================================================
# Hint registry tests
# =============================================================================

class TestHintRegistry:
    """Test hint registration and retrieval."""

    def test_get_hint_by_id(self):
        """Registered hints are retrievable by ID."""
        h = get_hint('_test.result_hint')
        assert h is not None
        assert h.id == '_test.result_hint'

    def test_get_hint_missing(self):
        """Missing hints return None."""
        assert get_hint('nonexistent') is None

    def test_get_hints_by_category(self):
        """Hints can be filtered by category."""
        test_hints = get_hints_by_category('test')
        assert len(test_hints) >= 3
        assert all(h.category == 'test' for h in test_hints)

    def test_domain_hints_registered(self):
        """Domain hints from utils.hints are available after import."""
        import utils.hints  # noqa: F401 — triggers registration
        assert get_hint('quantifier.use_for_any') is not None
        assert get_hint('bounds.implicit_defaults') is not None
        assert get_hint('iteration.large_space') is not None
        assert get_hint('format.pipe_safe') is not None


# =============================================================================
# Singleton tests
# =============================================================================

class TestSingleton:
    """Test module-level singleton management."""

    def test_init_output_returns_manager(self):
        """init_output returns an OutputManager."""
        mgr = init_output(verbosity=1, quiet=False)
        assert isinstance(mgr, OutputManager)
        assert mgr.verbosity == 1

    def test_get_output_returns_same(self):
        """get_output returns the previously initialized manager."""
        mgr1 = init_output(verbosity=2)
        mgr2 = get_output()
        assert mgr1 is mgr2

    def test_get_output_creates_default(self):
        """get_output creates a default manager if none initialized."""
        import utils.log_lib.manager as mgr_mod
        old = mgr_mod._manager
        try:
            mgr_mod._manager = None
            mgr = get_output()
            assert isinstance(mgr, OutputManager)
            assert mgr.verbosity == 0
        finally:
            mgr_mod._manager = old
