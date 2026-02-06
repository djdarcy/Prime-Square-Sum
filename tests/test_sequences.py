"""
Tests for mathematical sequence generators.
"""

import pytest
import numpy as np

from utils.sequences import (
    primesum, fibonacci, factorial, catalan, nth_prime,
    _ensure_int
)


class TestEnsureInt:
    """Tests for _ensure_int helper function."""

    def test_int_passthrough(self):
        """Test that ints pass through unchanged."""
        assert _ensure_int(7, "test") == 7
        assert _ensure_int(0, "test") == 0
        assert _ensure_int(-5, "test") == -5

    def test_integral_float_converted(self):
        """Test that integral floats are converted to int."""
        assert _ensure_int(7.0, "test") == 7
        assert _ensure_int(0.0, "test") == 0
        assert _ensure_int(100.0, "test") == 100

    def test_non_integral_float_raises(self):
        """Test that non-integral floats raise ValueError."""
        with pytest.raises(ValueError, match="requires integral value"):
            _ensure_int(7.5, "test")
        with pytest.raises(ValueError, match="requires integral value"):
            _ensure_int(0.1, "test")

    def test_numpy_int_converted(self):
        """Test that numpy integers are converted."""
        assert _ensure_int(np.int64(7), "test") == 7
        assert _ensure_int(np.int32(100), "test") == 100

    def test_invalid_type_raises(self):
        """Test that invalid types raise TypeError."""
        with pytest.raises(TypeError, match="requires int"):
            _ensure_int("7", "test")
        with pytest.raises(TypeError, match="requires int"):
            _ensure_int([7], "test")
        with pytest.raises(TypeError, match="requires int"):
            _ensure_int(None, "test")


class TestPrimesum:
    """Tests for primesum() function."""

    def test_primesum_known_value_666(self):
        """Test the famous primesum(7, 2) = 666."""
        assert primesum(7, 2) == 666

    def test_primesum_basic_cases(self):
        """Test basic primesum computations."""
        # First prime squared
        assert primesum(1, 2) == 4  # 2² = 4

        # First two primes squared
        assert primesum(2, 2) == 13  # 4 + 9 = 13

        # First three primes (linear sum)
        assert primesum(3, 1) == 10  # 2 + 3 + 5 = 10

    def test_primesum_zero_primes(self):
        """Test primesum(0) returns 0."""
        assert primesum(0, 2) == 0
        assert primesum(0, 1) == 0
        assert primesum(0, 3) == 0

    def test_primesum_power_zero(self):
        """Test primesum with power=0 (each prime^0 = 1)."""
        assert primesum(7, 0) == 7  # Sum of seven 1s
        assert primesum(10, 0) == 10

    def test_primesum_power_one(self):
        """Test primesum with power=1 (linear sum)."""
        assert primesum(1, 1) == 2
        assert primesum(2, 1) == 5  # 2 + 3
        assert primesum(3, 1) == 10  # 2 + 3 + 5
        assert primesum(4, 1) == 17  # 2 + 3 + 5 + 7

    def test_primesum_power_three(self):
        """Test primesum with power=3."""
        assert primesum(1, 3) == 8  # 2³
        assert primesum(2, 3) == 35  # 8 + 27

    def test_primesum_negative_n_raises(self):
        """Test that negative n raises ValueError."""
        with pytest.raises(ValueError, match="non-negative"):
            primesum(-1, 2)

    def test_primesum_accepts_float_n(self):
        """Test that integral float n is accepted."""
        assert primesum(7.0, 2) == 666
        assert primesum(7.0, 2.0) == 666

    def test_primesum_rejects_non_integral_float(self):
        """Test that non-integral float raises ValueError."""
        with pytest.raises(ValueError, match="integral"):
            primesum(7.5, 2)


class TestFibonacci:
    """Tests for fibonacci() function."""

    def test_fibonacci_base_cases(self):
        """Test fibonacci base cases."""
        assert fibonacci(0) == 0
        assert fibonacci(1) == 1
        assert fibonacci(2) == 1

    def test_fibonacci_sequence(self):
        """Test fibonacci sequence values."""
        # F(n): 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, ...
        expected = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
        for n, expected_val in enumerate(expected):
            assert fibonacci(n) == expected_val, f"fibonacci({n}) failed"

    def test_fibonacci_known_values(self):
        """Test known fibonacci values."""
        assert fibonacci(10) == 55
        assert fibonacci(20) == 6765
        assert fibonacci(30) == 832040

    def test_fibonacci_large_value(self):
        """Test fibonacci handles large values (arbitrary precision)."""
        # F(50) = 12586269025
        assert fibonacci(50) == 12586269025

    def test_fibonacci_negative_raises(self):
        """Test that negative n raises ValueError."""
        with pytest.raises(ValueError, match="non-negative"):
            fibonacci(-1)

    def test_fibonacci_accepts_float(self):
        """Test that integral float is accepted."""
        assert fibonacci(10.0) == 55

    def test_fibonacci_rejects_non_integral_float(self):
        """Test that non-integral float raises ValueError."""
        with pytest.raises(ValueError, match="integral"):
            fibonacci(10.5)


class TestFactorial:
    """Tests for factorial() function."""

    def test_factorial_base_cases(self):
        """Test factorial base cases."""
        assert factorial(0) == 1
        assert factorial(1) == 1

    def test_factorial_known_values(self):
        """Test known factorial values."""
        assert factorial(2) == 2
        assert factorial(3) == 6
        assert factorial(4) == 24
        assert factorial(5) == 120
        assert factorial(10) == 3628800

    def test_factorial_large_value(self):
        """Test factorial handles large values."""
        # 20! = 2432902008176640000
        assert factorial(20) == 2432902008176640000

    def test_factorial_negative_raises(self):
        """Test that negative n raises ValueError."""
        with pytest.raises(ValueError, match="non-negative"):
            factorial(-1)

    def test_factorial_accepts_float(self):
        """Test that integral float is accepted."""
        assert factorial(5.0) == 120

    def test_factorial_rejects_non_integral_float(self):
        """Test that non-integral float raises ValueError."""
        with pytest.raises(ValueError, match="integral"):
            factorial(5.5)


class TestCatalan:
    """Tests for catalan() function."""

    def test_catalan_base_cases(self):
        """Test catalan base cases."""
        assert catalan(0) == 1
        assert catalan(1) == 1

    def test_catalan_sequence(self):
        """Test catalan sequence values (OEIS A000108)."""
        # C(n): 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, ...
        expected = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]
        for n, expected_val in enumerate(expected):
            assert catalan(n) == expected_val, f"catalan({n}) failed"

    def test_catalan_known_values(self):
        """Test known catalan values."""
        assert catalan(3) == 5
        assert catalan(5) == 42
        assert catalan(10) == 16796

    def test_catalan_large_value(self):
        """Test catalan handles large values."""
        # C(20) = 6564120420
        assert catalan(20) == 6564120420

    def test_catalan_negative_raises(self):
        """Test that negative n raises ValueError."""
        with pytest.raises(ValueError, match="non-negative"):
            catalan(-1)

    def test_catalan_accepts_float(self):
        """Test that integral float is accepted."""
        assert catalan(5.0) == 42

    def test_catalan_rejects_non_integral_float(self):
        """Test that non-integral float raises ValueError."""
        with pytest.raises(ValueError, match="integral"):
            catalan(5.5)


class TestNthPrime:
    """Tests for nth_prime() re-export."""

    def test_nth_prime_basic(self):
        """Test basic nth_prime values."""
        assert nth_prime(1) == 2
        assert nth_prime(2) == 3
        assert nth_prime(3) == 5
        assert nth_prime(4) == 7
        assert nth_prime(5) == 11
        assert nth_prime(6) == 13
        assert nth_prime(7) == 17

    def test_nth_prime_larger_values(self):
        """Test larger nth_prime values."""
        assert nth_prime(100) == 541
        assert nth_prime(1000) == 7919


class TestFunctionRegistryIntegration:
    """Tests for FunctionRegistry integration with sequences."""

    def test_sequences_registered(self):
        """Test that all sequence functions are registered."""
        from utils.function_registry import FunctionRegistry

        registry = FunctionRegistry()

        assert "primesum" in registry
        assert "fibonacci" in registry
        assert "factorial" in registry
        assert "catalan" in registry
        # nth_prime was already registered from sieve
        assert "nth_prime" in registry

    def test_sequences_callable_from_registry(self):
        """Test that sequences can be called via registry."""
        from utils.function_registry import FunctionRegistry

        registry = FunctionRegistry()

        assert registry.get("primesum")(7, 2) == 666
        assert registry.get("fibonacci")(10) == 55
        assert registry.get("factorial")(5) == 120
        assert registry.get("catalan")(5) == 42

    def test_sequences_have_metadata(self):
        """Test that sequences have proper metadata."""
        from utils.function_registry import FunctionRegistry

        registry = FunctionRegistry()

        # primesum has 1 required arg (n), power has default
        sig = registry.get_signature("primesum")
        assert sig.arg_count == 1  # Only n is required
        assert sig.source == "builtin"
        assert len(sig.doc) > 0

        # fibonacci has 1 required arg
        sig = registry.get_signature("fibonacci")
        assert sig.arg_count == 1
        assert sig.source == "builtin"

    def test_registry_builtin_count(self):
        """Test total number of registered builtins."""
        from utils.function_registry import FunctionRegistry

        registry = FunctionRegistry()

        # 6 original (tri, qtri, trisum, is_triangular, digital_root, nth_prime)
        # + 4 sequences (primesum, fibonacci, factorial, catalan)
        # + 1 arithmetic (square)
        # = 11 total
        assert len(registry) == 11
