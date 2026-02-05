"""
End-to-end CLI integration tests.

These tests actually invoke prime-square-sum.py as a subprocess
to verify the CLI works correctly.

Issue: #18 (CLI rewrite)
Epic: #13 (Generalized Expression Grammar)
"""

import subprocess
import sys
import json
import pytest
from pathlib import Path

# Path to the main script
SCRIPT = Path(__file__).parent.parent / "prime-square-sum.py"


def run_cli(*args, timeout=30):
    """Run the CLI and return (returncode, stdout, stderr)."""
    cmd = [sys.executable, str(SCRIPT)] + list(args)
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return result.returncode, result.stdout, result.stderr


# =============================================================================
# Basic Functionality Tests
# =============================================================================

class TestBasicCLI:
    """Test basic CLI invocation."""

    def test_version(self):
        """--version shows version number."""
        code, stdout, stderr = run_cli("--version")
        assert code == 0
        assert "0.7" in stdout  # Version 0.7.x

    def test_help(self):
        """--help shows usage information."""
        code, stdout, stderr = run_cli("--help")
        assert code == 0
        assert "--expr" in stdout
        assert "--target" in stdout
        assert "--lhs" in stdout

    def test_list_functions(self):
        """--list-functions shows available functions."""
        code, stdout, stderr = run_cli("--list-functions")
        assert code == 0
        assert "primesum" in stdout
        assert "tri" in stdout
        assert "fibonacci" in stdout

    def test_no_args_shows_error(self):
        """Running without arguments shows helpful error."""
        code, stdout, stderr = run_cli()
        assert code != 0
        assert "required" in stderr.lower() or "error" in stderr.lower()


# =============================================================================
# Tier 1: Full Expression Tests
# =============================================================================

class TestFullExpression:
    """Test --expr flag with full expressions."""

    def test_expr_does_exist_match(self):
        """--expr finds match for known value."""
        code, stdout, stderr = run_cli(
            "--expr", "does_exist primesum(n,2) == 666"
        )
        assert code == 0
        assert "n=7" in stdout

    def test_expr_does_exist_no_match(self):
        """--expr returns no match for impossible value."""
        code, stdout, stderr = run_cli(
            "--expr", "does_exist primesum(n,2) == 12345",
            "--max-n", "100"
        )
        assert code == 1  # No match returns exit code 1
        assert "No match" in stdout or "not found" in stdout.lower()

    def test_expr_for_any_finds_match(self):
        """--expr with for_any finds matches."""
        code, stdout, stderr = run_cli(
            "--expr", "for_any primesum(n,2) == tri(m)",
            "--max-n", "10",
            "--max-m", "50"
        )
        assert code == 0
        assert "n=7" in stdout
        assert "m=36" in stdout


# =============================================================================
# Tier 2: Decomposed Flags Tests
# =============================================================================

class TestDecomposedFlags:
    """Test decomposed flags (--lhs, --rhs, etc.)."""

    def test_target_only(self):
        """--target with defaults finds match."""
        code, stdout, stderr = run_cli("--target", "666")
        assert code == 0
        assert "n=7" in stdout

    def test_rhs_alias(self):
        """--rhs is alias for --target."""
        code, stdout, stderr = run_cli("--rhs", "666")
        assert code == 0
        assert "n=7" in stdout

    def test_custom_lhs(self):
        """--lhs overrides default left-hand side."""
        code, stdout, stderr = run_cli(
            "--lhs", "tri(n)",
            "--target", "666",
            "--max-n", "100"
        )
        assert code == 0
        assert "n=36" in stdout  # tri(36) = 666

    def test_custom_operator(self):
        """--operator changes comparison."""
        code, stdout, stderr = run_cli(
            "--lhs", "tri(n)",
            "--operator", ">=",
            "--target", "100",
            "--max-n", "20"
        )
        assert code == 0
        # tri(13) = 91, tri(14) = 105
        assert "n=14" in stdout

    def test_quantifier_for_any(self):
        """--quantifier for_any finds all matches."""
        code, stdout, stderr = run_cli(
            "--quantifier", "for_any",
            "--lhs", "tri(n)",
            "--target", "tri(m)",
            "--max-n", "5",
            "--max-m", "5"
        )
        assert code == 0
        # Should find matches where tri(n) == tri(m), i.e., n == m
        assert "Found" in stdout


# =============================================================================
# Output Format Tests
# =============================================================================

class TestOutputFormats:
    """Test different output formats."""

    def test_text_format(self):
        """--format text (default) shows human-readable output."""
        code, stdout, stderr = run_cli(
            "--target", "666",
            "--format", "text"
        )
        assert code == 0
        assert "Found:" in stdout
        assert "n=7" in stdout

    def test_json_format(self):
        """--format json outputs valid JSON."""
        code, stdout, stderr = run_cli(
            "--target", "666",
            "--format", "json"
        )
        assert code == 0
        # Parse the JSON (ignoring stderr warnings)
        data = json.loads(stdout.strip())
        assert data["found"] is True
        assert data["variables"]["n"] == 7

    def test_csv_format(self):
        """--format csv outputs CSV-style."""
        code, stdout, stderr = run_cli(
            "--target", "666",
            "--format", "csv"
        )
        assert code == 0
        assert "n=7" in stdout


# =============================================================================
# Verify Quantifier Tests (Issue #34)
# =============================================================================

class TestVerifyQuantifier:
    """Test verify quantifier for closed formulas."""

    def test_verify_explicit_true(self):
        """Explicit verify returns 'true' for true formula."""
        code, stdout, stderr = run_cli(
            "--expr", "verify primesum(7,2) == 666"
        )
        assert code == 0
        assert "true" in stdout.lower()

    def test_verify_explicit_false(self):
        """Explicit verify returns 'false' for false formula."""
        code, stdout, stderr = run_cli(
            "--expr", "verify primesum(7,2) == 667"
        )
        # Note: verify false still exits 0 (it worked, answer is false)
        # The expression evaluated successfully, result is false
        assert "false" in stdout.lower()

    def test_verify_implicit(self):
        """Implicit verify (no quantifier, no free vars) works."""
        code, stdout, stderr = run_cli(
            "--expr", "tri(36) == 666"
        )
        assert code == 0
        assert "true" in stdout.lower()

    def test_verify_json_output(self):
        """Verify with JSON output format."""
        code, stdout, stderr = run_cli(
            "--expr", "verify primesum(7,2) == 666",
            "--format", "json"
        )
        assert code == 0
        assert '"verified": true' in stdout or '"verified":true' in stdout

    def test_verify_primesum_values(self):
        """Verify primesum values with different powers.

        Sum of squared primes (power=2):
          primesum(1,2) = 2^2 = 4
          primesum(2,2) = 2^2 + 3^2 = 4 + 9 = 13

        Sum of primes (power=1):
          primesum(2,1) = 2 + 3 = 5
        """
        # primesum(1,2) = 2^2 = 4
        code, stdout, stderr = run_cli("--expr", "verify primesum(1,2) == 4")
        assert code == 0
        assert "true" in stdout.lower()

        # primesum(2,2) = 2^2 + 3^2 = 4 + 9 = 13
        code, stdout, stderr = run_cli("--expr", "verify primesum(2,2) == 13")
        assert code == 0
        assert "true" in stdout.lower()

        # primesum(2,1) = 2 + 3 = 5 (sum of primes, not squared)
        code, stdout, stderr = run_cli("--expr", "verify primesum(2,1) == 5")
        assert code == 0
        assert "true" in stdout.lower()

        # Verify false output: 5 is NOT a sum of squared primes
        # (primesum(1,2)=4, primesum(2,2)=13, gap skips 5)
        code, stdout, stderr = run_cli("--expr", "verify primesum(1,2) == 5")
        assert code == 0  # verify succeeded, answer is false
        assert "false" in stdout.lower()


# =============================================================================
# Verbose Mode Tests
# =============================================================================

class TestVerboseMode:
    """Test --verbose flag."""

    def test_verbose_shows_expression(self):
        """--verbose shows the parsed expression."""
        code, stdout, stderr = run_cli(
            "--target", "666",
            "--verbose"
        )
        assert code == 0
        assert "Expression:" in stdout
        assert "primesum" in stdout

    def test_verbose_shows_timing(self):
        """--verbose shows timing information."""
        code, stdout, stderr = run_cli(
            "--target", "666",
            "--verbose"
        )
        assert code == 0
        assert "Time:" in stdout


# =============================================================================
# Error Handling Tests
# =============================================================================

class TestErrorHandling:
    """Test error handling for invalid inputs."""

    def test_invalid_expression_syntax(self):
        """Invalid expression syntax shows parse error."""
        code, stdout, stderr = run_cli(
            "--expr", "this is not valid syntax"
        )
        assert code == 1
        assert "error" in stderr.lower() or "error" in stdout.lower()

    def test_unknown_function(self):
        """Unknown function results in no match (silently fails during iteration).

        Note: Currently, unknown functions are caught during iteration and
        silently skipped. A future enhancement could validate functions
        before iteration starts.
        """
        code, stdout, stderr = run_cli(
            "--expr", "does_exist unknown_func(n) == 666",
            "--max-n", "10"
        )
        # Currently returns "no match" rather than an error
        # This is because EvaluationError is caught during iteration
        assert code == 1
        assert "No match" in stdout or "not found" in stdout.lower()

    def test_missing_rhs_with_lhs(self):
        """--lhs without --rhs shows error."""
        code, stdout, stderr = run_cli(
            "--lhs", "tri(n)"
        )
        assert code != 0
