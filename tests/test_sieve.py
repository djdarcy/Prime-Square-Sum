"""
test_sieve.py - Unit tests for sieve module
=============================================

Tests all sieve algorithms: basic, segmented, individual, and primesieve.
Verifies correctness, edge cases, and algorithm selection logic.
"""

import pytest
import numpy as np
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.sieve import (
    generate_primes, generate_n_primes, generate_primes_range,
    nth_prime, prime_count, get_available_algorithms, get_algorithm_info,
    _basic_sieve, _segmented_sieve, _individual_sieve, _python_sieve,
    _select_python_algorithm, _calculate_segment_size,
    ALGORITHM_AUTO, ALGORITHM_BASIC, ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL,
    ALGORITHM_PRIMESIEVE, PRIMESIEVE_AVAILABLE,
)


# Known prime counts for verification
# https://primes.utm.edu/howmany.html
PRIME_COUNTS = {
    10: 4,           # 2, 3, 5, 7
    100: 25,
    1000: 168,
    10000: 1229,
    100000: 9592,
    1000000: 78498,
}

# Known nth primes (1-indexed)
NTH_PRIMES = {
    1: 2,
    7: 17,
    100: 541,
    1000: 7919,
}


class TestBasicSieve:
    """Test the basic Sieve of Eratosthenes implementation."""

    def test_basic_sieve_small(self):
        """Test basic sieve with small limits."""
        assert list(_basic_sieve(2)) == []
        assert list(_basic_sieve(3)) == [2]
        assert list(_basic_sieve(10)) == [2, 3, 5, 7]
        assert list(_basic_sieve(20)) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_basic_sieve_edge_cases(self):
        """Test basic sieve edge cases."""
        assert len(_basic_sieve(0)) == 0
        assert len(_basic_sieve(1)) == 0
        assert len(_basic_sieve(-5)) == 0

    def test_basic_sieve_prime_counts(self):
        """Test basic sieve produces correct prime counts."""
        for limit, expected_count in PRIME_COUNTS.items():
            primes = _basic_sieve(limit)
            assert len(primes) == expected_count, f"Failed for limit={limit}"

    def test_basic_sieve_first_primes(self):
        """Test basic sieve produces correct first primes."""
        primes = _basic_sieve(100)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                    53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
        assert list(primes) == expected


class TestSegmentedSieve:
    """Test the segmented sieve implementation."""

    def test_segmented_sieve_matches_basic(self):
        """Test segmented sieve produces same results as basic sieve."""
        for limit in [100, 1000, 10000, 100000]:
            basic = _basic_sieve(limit)
            segmented = _segmented_sieve(limit)
            assert np.array_equal(basic, segmented), f"Mismatch at limit={limit}"

    def test_segmented_sieve_various_segment_sizes(self):
        """Test segmented sieve with various segment sizes."""
        limit = 100000
        basic = _basic_sieve(limit)

        for segment_size in [1000, 5000, 10000, 33333, 50000]:
            segmented = _segmented_sieve(limit, segment_size=segment_size)
            assert np.array_equal(basic, segmented), \
                f"Mismatch with segment_size={segment_size}"

    def test_segmented_sieve_small_limits(self):
        """Test segmented sieve with limits smaller than segment size."""
        for limit in [10, 50, 100, 500]:
            basic = _basic_sieve(limit)
            # Segment size larger than limit
            segmented = _segmented_sieve(limit, segment_size=10000)
            assert np.array_equal(basic, segmented), f"Mismatch at limit={limit}"

    def test_segmented_sieve_edge_cases(self):
        """Test segmented sieve edge cases."""
        assert len(_segmented_sieve(0)) == 0
        assert len(_segmented_sieve(1)) == 0
        assert len(_segmented_sieve(2)) == 0
        assert list(_segmented_sieve(3)) == [2]

    def test_segmented_sieve_segment_boundaries(self):
        """Test segmented sieve handles segment boundaries correctly."""
        # Use segment size that creates interesting boundaries
        limit = 1000
        for segment_size in [100, 101, 99, 333]:
            basic = _basic_sieve(limit)
            segmented = _segmented_sieve(limit, segment_size=segment_size)
            assert np.array_equal(basic, segmented), \
                f"Boundary issue with segment_size={segment_size}"


class TestIndividualSieve:
    """Test the individual primality testing implementation."""

    def test_individual_sieve_matches_basic(self):
        """Test individual sieve produces same results as basic sieve."""
        for limit in [100, 500, 1000]:
            basic = _basic_sieve(limit)
            individual = _individual_sieve(limit)
            assert np.array_equal(basic, individual), f"Mismatch at limit={limit}"

    def test_individual_sieve_edge_cases(self):
        """Test individual sieve edge cases."""
        assert len(_individual_sieve(0)) == 0
        assert len(_individual_sieve(1)) == 0
        assert len(_individual_sieve(2)) == 0
        assert list(_individual_sieve(3)) == [2]
        assert list(_individual_sieve(4)) == [2, 3]


class TestPythonSieveFacade:
    """Test the _python_sieve facade/dispatcher.

    Note: These tests call _python_sieve() directly to exercise the Python
    fallback algorithms (basic, segmented, individual). This triggers a
    "primesieve not available" warning even when primesieve IS installed —
    that warning is expected and confirms the fallback path is being tested.
    """

    def test_python_sieve_auto_selection(self):
        """Test that auto-selection works correctly."""
        primes = _python_sieve(1000, algorithm=ALGORITHM_AUTO)
        assert len(primes) == 168

    def test_python_sieve_explicit_algorithms(self):
        """Test explicit algorithm selection through facade."""
        limit = 10000
        expected = _basic_sieve(limit)

        for algo in [ALGORITHM_BASIC, ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
            result = _python_sieve(limit, algorithm=algo)
            assert np.array_equal(expected, result), f"Mismatch with {algo}"

    def test_python_sieve_invalid_algorithm(self):
        """Test that invalid algorithm raises error."""
        with pytest.raises(ValueError, match="Unknown"):
            _python_sieve(1000, algorithm="invalid_algo")


class TestAlgorithmSelection:
    """Test the algorithm auto-selection logic."""

    def test_select_minimal_preference(self):
        """Test that 'minimal' preference selects individual."""
        algo = _select_python_algorithm(1000000, prefer="minimal")
        assert algo == ALGORITHM_INDIVIDUAL

    def test_select_memory_preference(self):
        """Test that 'memory' preference influences selection."""
        # With large memory available, should prefer basic
        algo = _select_python_algorithm(1000, max_memory_mb=1000, prefer="memory")
        assert algo == ALGORITHM_BASIC

    def test_select_constrained_memory(self):
        """Test selection with constrained memory."""
        # 1GB limit but 10GB needed -> should select segmented
        algo = _select_python_algorithm(10_000_000_000, max_memory_mb=1000)
        assert algo == ALGORITHM_SEGMENTED

    def test_select_tiny_memory(self):
        """Test selection with very limited memory."""
        # 100MB needed but only 15MB available -> should use segmented (>=10MB threshold)
        algo = _select_python_algorithm(100_000_000, max_memory_mb=15)
        assert algo == ALGORITHM_SEGMENTED

        # Extreme case: less than 10MB available -> individual
        algo = _select_python_algorithm(100_000_000, max_memory_mb=5)
        assert algo == ALGORITHM_INDIVIDUAL


class TestSegmentSizeCalculation:
    """Test segment size calculation."""

    def test_segment_size_bounds(self):
        """Test segment size respects min/max bounds."""
        # Should be at least MIN_SEGMENT_SIZE
        size = _calculate_segment_size(1000000, max_memory_mb=0)
        assert size >= 1_000_000  # MIN_SEGMENT_SIZE

        # Should be at most MAX_SEGMENT_SIZE
        size = _calculate_segment_size(1000000000, max_memory_mb=10000)
        assert size <= 100_000_000  # MAX_SEGMENT_SIZE

    def test_segment_size_respects_limit(self):
        """Test segment size doesn't exceed limit."""
        size = _calculate_segment_size(1000, max_memory_mb=100)
        assert size <= 1000


class TestGeneratePrimes:
    """Test the main generate_primes function."""

    def test_generate_primes_default(self):
        """Test generate_primes with default settings."""
        primes = generate_primes(100)
        assert len(primes) == 25
        assert list(primes[:5]) == [2, 3, 5, 7, 11]

    def test_generate_primes_with_algorithm(self):
        """Test generate_primes with explicit algorithm."""
        for algo in [ALGORITHM_BASIC, ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
            primes = generate_primes(1000, algorithm=algo)
            assert len(primes) == 168, f"Wrong count with {algo}"

    def test_generate_primes_invalid_algorithm(self):
        """Test generate_primes with invalid algorithm raises error."""
        with pytest.raises(ValueError, match="Unknown algorithm"):
            generate_primes(100, algorithm="bogus")

    @pytest.mark.skipif(not PRIMESIEVE_AVAILABLE, reason="primesieve not installed")
    def test_generate_primes_primesieve(self):
        """Test generate_primes with primesieve."""
        primes = generate_primes(10000, algorithm=ALGORITHM_PRIMESIEVE)
        assert len(primes) == 1229

    def test_generate_primes_primesieve_unavailable(self):
        """Test that requesting primesieve when unavailable raises error."""
        if PRIMESIEVE_AVAILABLE:
            pytest.skip("primesieve is available")
        with pytest.raises(ValueError, match="not installed"):
            generate_primes(100, algorithm=ALGORITHM_PRIMESIEVE)


class TestGenerateNPrimes:
    """Test generate_n_primes function."""

    def test_generate_n_primes_small(self):
        """Test generating small numbers of primes."""
        assert list(generate_n_primes(1)) == [2]
        assert list(generate_n_primes(4)) == [2, 3, 5, 7]
        assert list(generate_n_primes(7)) == [2, 3, 5, 7, 11, 13, 17]

    def test_generate_n_primes_edge_cases(self):
        """Test generate_n_primes edge cases."""
        assert len(generate_n_primes(0)) == 0
        assert len(generate_n_primes(-5)) == 0

    def test_generate_n_primes_with_algorithm(self):
        """Test generate_n_primes with explicit algorithm."""
        for algo in [ALGORITHM_BASIC, ALGORITHM_SEGMENTED]:
            primes = generate_n_primes(100, algorithm=algo)
            assert len(primes) == 100
            assert primes[-1] == 541  # 100th prime


class TestNthPrime:
    """Test nth_prime function."""

    def test_nth_prime_known_values(self):
        """Test nth_prime with known values."""
        for n, expected in NTH_PRIMES.items():
            assert nth_prime(n) == expected, f"Failed for n={n}"

    def test_nth_prime_invalid_input(self):
        """Test nth_prime with invalid input."""
        with pytest.raises(ValueError):
            nth_prime(0)
        with pytest.raises(ValueError):
            nth_prime(-1)


class TestPrimeCount:
    """Test prime_count function."""

    def test_prime_count_known_values(self):
        """Test prime_count with known values."""
        for limit, expected in PRIME_COUNTS.items():
            # prime_count(n) counts primes <= n, so use limit-1 for exclusive
            count = prime_count(limit - 1)
            assert count == expected, f"Failed for limit={limit}"


class TestGetAlgorithmInfo:
    """Test algorithm information functions."""

    def test_get_available_algorithms(self):
        """Test get_available_algorithms returns valid list."""
        algos = get_available_algorithms()
        assert ALGORITHM_AUTO in algos
        assert ALGORITHM_BASIC in algos
        assert ALGORITHM_SEGMENTED in algos
        assert ALGORITHM_INDIVIDUAL in algos
        if PRIMESIEVE_AVAILABLE:
            assert ALGORITHM_PRIMESIEVE in algos

    def test_get_algorithm_info(self):
        """Test get_algorithm_info returns complete info."""
        info = get_algorithm_info()
        assert ALGORITHM_AUTO in info
        assert ALGORITHM_BASIC in info
        assert info[ALGORITHM_BASIC]["available"] is True
        assert "description" in info[ALGORITHM_BASIC]


class TestPrimeSumCompatibility:
    """Test that sieve works correctly for primesum use case."""

    def test_primesum_666(self):
        """Test the classic primesum(7, 2) = 666 case."""
        primes = generate_n_primes(7)
        sum_of_squares = sum(p ** 2 for p in primes)
        assert sum_of_squares == 666

    def test_primesum_666_all_algorithms(self):
        """Test primesum calculation works with all algorithms."""
        for algo in [ALGORITHM_BASIC, ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
            primes = generate_n_primes(7, algorithm=algo)
            sum_of_squares = sum(p ** 2 for p in primes)
            assert sum_of_squares == 666, f"Failed with {algo}"
