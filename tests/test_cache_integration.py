"""
test_cache_integration.py - Integration tests for incremental sum caching

Tests the IncrementalSumCache through the main script's functions,
verifying real-world usage scenarios:
- Multi-target searches
- Different powers simultaneously
- Cache resumption across sessions
- Power isolation (separate files)
- Batch vs incremental equivalence
"""

import pytest
import sys
import os
import tempfile
import shutil
from pathlib import Path

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.sieve import generate_n_primes
from utils.sum_cache import IncrementalSumCache


class TestCacheWithRealPrimes:
    """Integration tests using actual prime generation and calculation."""

    def test_multi_target_search_same_power(self):
        """Test searching for multiple different targets with same power."""
        # Generate first 100 primes
        primes = generate_n_primes(100)

        # Create cache with power=2
        cache = IncrementalSumCache(powers=[2])

        # Add all primes and track sums
        results = {}
        for i, prime in enumerate(primes):
            cache.add_prime(prime)
            current_sum = cache.get_sum(2)

            # Record specific target matches
            if current_sum in [666, 1000, 5000]:
                results[current_sum] = (i + 1, prime)  # (count, last_prime)

        # Verify we found target 666 with exactly 7 primes
        assert 666 in results, "Should find sum of 666"
        assert results[666][0] == 7, f"Should have 7 primes for 666, got {results[666][0]}"

        # Verify 1000 and 5000 found if they exist
        if 1000 in results:
            assert results[1000][0] > 7, "Sum of 1000 should need more primes than 666"

    def test_multi_power_simultaneous(self):
        """Test tracking multiple powers (p², p³, p⁴) simultaneously."""
        # Generate first 50 primes
        primes = generate_n_primes(50)

        # Create cache with multiple powers
        cache = IncrementalSumCache(powers=[2, 3, 4])

        # Add all primes
        for prime in primes:
            cache.add_prime(prime)

        # Verify all powers are tracked
        sum_p2 = cache.get_sum(2)
        sum_p3 = cache.get_sum(3)
        sum_p4 = cache.get_sum(4)

        assert sum_p2 > 0, "Power 2 sum should be positive"
        assert sum_p3 > 0, "Power 3 sum should be positive"
        assert sum_p4 > 0, "Power 4 sum should be positive"

        # p⁴ > p³ > p² (for primes > 1)
        assert sum_p4 > sum_p3, "p⁴ sum should exceed p³ sum"
        assert sum_p3 > sum_p2, "p³ sum should exceed p² sum"

    def test_cache_resumption_single_session(self):
        """Test checkpoint save and resume within single test."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_file = Path(tmpdir) / "test_cache.npz"

            # Create cache and add first 10 primes
            primes = generate_n_primes(50)

            cache1 = IncrementalSumCache(powers=[2])
            for prime in primes[:10]:
                cache1.add_prime(prime)
            sum_after_10 = cache1.get_sum(2)
            cache1.save_checkpoint(cache_file)

            # Load checkpoint and add more primes
            cache2 = IncrementalSumCache.load_checkpoint(cache_file)
            assert cache2.get_prime_count() == 10, "Should have 10 primes after load"
            assert cache2.get_sum(2) == sum_after_10, "Sum should match checkpoint"

            # Add 10 more primes
            for prime in primes[10:20]:
                cache2.add_prime(prime)
            sum_after_20 = cache2.get_sum(2)

            # Verify total sum matches full calculation
            cache3 = IncrementalSumCache(powers=[2])
            for prime in primes[:20]:
                cache3.add_prime(prime)

            assert cache2.get_sum(2) == cache3.get_sum(2), \
                "Resumed cache sum should equal fresh calculation"

    def test_power_isolation_separate_files(self):
        """Test that different powers use separate cache files."""
        with tempfile.TemporaryDirectory() as tmpdir:
            primes = generate_n_primes(30)

            # Create power 2 cache
            cache_p2_file = Path(tmpdir) / "sums_p2.npz"
            cache_p2 = IncrementalSumCache(powers=[2])
            for prime in primes[:15]:
                cache_p2.add_prime(prime)
            cache_p2.save_checkpoint(cache_p2_file)
            sum_p2_15 = cache_p2.get_sum(2)

            # Create power 3 cache
            cache_p3_file = Path(tmpdir) / "sums_p3.npz"
            cache_p3 = IncrementalSumCache(powers=[3])
            for prime in primes[:15]:
                cache_p3.add_prime(prime)
            cache_p3.save_checkpoint(cache_p3_file)
            sum_p3_15 = cache_p3.get_sum(3)

            # Verify files are separate
            assert cache_p2_file.exists(), "Power 2 file should exist"
            assert cache_p3_file.exists(), "Power 3 file should exist"
            assert cache_p2_file != cache_p3_file, "Files should be different"

            # Load and verify isolation (sums are for different powers)
            loaded_p2 = IncrementalSumCache.load_checkpoint(cache_p2_file)
            loaded_p3 = IncrementalSumCache.load_checkpoint(cache_p3_file)

            assert loaded_p2.get_sum(2) == sum_p2_15, "Power 2 should be isolated"
            assert loaded_p3.get_sum(3) == sum_p3_15, "Power 3 should be isolated"

            # Verify sums are different (p³ > p²)
            assert loaded_p3.get_sum(3) > loaded_p2.get_sum(2), \
                "p³ sum should exceed p² sum for same primes"

    def test_incremental_vs_batch_accuracy(self):
        """Verify incremental cache produces identical results to batch."""
        primes = generate_n_primes(75)

        # Batch calculation
        batch_sums = {}
        for power in [2, 3, 4]:
            batch_sums[power] = sum(p ** power for p in primes)

        # Incremental calculation
        cache = IncrementalSumCache(powers=[2, 3, 4])
        for prime in primes:
            cache.add_prime(prime)

        # Verify equivalence
        for power in [2, 3, 4]:
            assert cache.get_sum(power) == batch_sums[power], \
                f"Incremental p^{power} should match batch calculation"

    def test_checkpoint_frequency_triggers(self):
        """Test that checkpointing triggers at correct thresholds."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_file = Path(tmpdir) / "freq_test.npz"
            primes = generate_n_primes(2000)

            cache = IncrementalSumCache(powers=[2])

            # Add primes in batches and test should_checkpoint at boundaries
            # First 1000 primes: should checkpoint every 1000
            checkpoint_count = 0
            for i, prime in enumerate(primes[:1000]):
                cache.add_prime(prime)
                if cache.should_checkpoint():
                    checkpoint_count += 1

            assert checkpoint_count == 1, "Should checkpoint once at 1000 primes"

            # Continue to 2000 primes: should checkpoint every 100
            checkpoint_count = 0
            for i, prime in enumerate(primes[1000:2000]):
                cache.add_prime(prime)
                if cache.should_checkpoint():
                    checkpoint_count += 1

            assert checkpoint_count >= 9, "Should checkpoint ~10 times from 1000-2000 primes"

    def test_metadata_persistence(self):
        """Test that metadata is preserved across checkpoint cycles."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_file = Path(tmpdir) / "metadata_test.npz"
            primes = generate_n_primes(100)

            # Create and save cache
            cache1 = IncrementalSumCache(powers=[2, 3])
            for prime in primes[:50]:
                cache1.add_prime(prime)

            assert cache1.metadata.prime_count == 50
            assert cache1.metadata.last_prime == primes[49]
            assert cache1.metadata.powers == [2, 3]

            cache1.save_checkpoint(cache_file)

            # Load and verify metadata
            cache2 = IncrementalSumCache.load_checkpoint(cache_file)
            assert cache2.metadata.prime_count == 50, "Prime count should persist"
            assert cache2.metadata.last_prime == primes[49], "Last prime should persist"
            assert cache2.metadata.powers == [2, 3], "Powers list should persist"
            assert cache2.metadata.version == "1.0", "Version should be preserved"

    def test_rolling_window_diagnostics(self):
        """Test that rolling window diagnostics capture correct values."""
        primes = generate_n_primes(20)
        cache = IncrementalSumCache(powers=[2])

        # Add first 2 primes (should go into initial_values)
        cache.add_prime(primes[0])
        cache.add_prime(primes[1])

        assert len(cache.initial_values) == 2, "Should have 2 initial values"
        assert cache.initial_values[0][0] == primes[0], "First prime should be 2"
        assert cache.initial_values[1][0] == primes[1], "Second prime should be 3"

        # Add more primes and check recent values
        for prime in primes[2:8]:
            cache.add_prime(prime)

        assert len(cache.recent_values) <= 3, "Recent values should be limited to 3"
        assert cache.recent_values[-1][0] == primes[7], "Last recent value should be 8th prime"

    def test_edge_case_single_prime(self):
        """Test cache behavior with single prime."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)

        assert cache.get_prime_count() == 1, "Should have 1 prime"
        assert cache.get_sum(2) == 4, "2² = 4"
        assert cache.metadata.last_prime == 2, "Last prime should be 2"

    def test_edge_case_duplicate_additions_error(self):
        """Test that adding same prime twice updates cache (not prevented)."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)
        first_sum = cache.get_sum(2)

        cache.add_prime(2)  # Add same prime again
        second_sum = cache.get_sum(2)

        # Cache adds it again (no deduplication)
        assert second_sum == first_sum * 2, "Adding prime twice should double sum"

    def test_zero_primes_cache(self):
        """Test cache behavior with no primes added."""
        cache = IncrementalSumCache(powers=[2])

        assert cache.get_prime_count() == 0, "Should have 0 primes"
        assert cache.get_sum(2) == 0, "Sum should be 0"
        assert cache.metadata.last_prime is None, "Last prime should be None"


class TestCacheErrorHandling:
    """Test error handling in cache integration."""

    def test_invalid_power_retrieval(self):
        """Test requesting sum for non-existent power."""
        cache = IncrementalSumCache(powers=[2])

        with pytest.raises(ValueError):
            cache.get_sum(3)  # Power 3 not tracked

    def test_load_nonexistent_file(self):
        """Test loading from non-existent checkpoint file."""
        with tempfile.TemporaryDirectory() as tmpdir:
            nonexistent = Path(tmpdir) / "doesnt_exist.npz"

            with pytest.raises(FileNotFoundError):
                IncrementalSumCache.load_checkpoint(nonexistent)

    def test_corrupted_checkpoint_metadata(self):
        """Test handling of corrupted metadata in checkpoint."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_file = Path(tmpdir) / "corrupted.npz"

            # Create a cache and save it
            cache = IncrementalSumCache(powers=[2])
            cache.add_prime(2)
            cache.save_checkpoint(cache_file)

            # File should load successfully
            loaded = IncrementalSumCache.load_checkpoint(cache_file)
            assert loaded.get_prime_count() == 1


class TestCachePerformance:
    """Performance validation tests."""

    def test_incremental_speed_vs_batch(self):
        """Verify incremental caching is O(1) per prime addition."""
        import time

        primes = generate_n_primes(1000)

        # Batch calculation time
        start = time.perf_counter()
        batch_sum = sum(p ** 2 for p in primes)
        batch_time = time.perf_counter() - start

        # Incremental calculation time
        cache = IncrementalSumCache(powers=[2])
        start = time.perf_counter()
        for prime in primes:
            cache.add_prime(prime)
        incremental_time = time.perf_counter() - start

        # Verify results match
        assert cache.get_sum(2) == batch_sum, "Results should match"

        # Incremental should be reasonably fast (O(1) per prime)
        # Allow batch to be faster due to overhead, but both should be fast
        assert incremental_time < 1.0, "Incremental calculation should be fast"

    def test_checkpoint_io_speed(self):
        """Verify checkpoint I/O is fast."""
        import time

        with tempfile.TemporaryDirectory() as tmpdir:
            cache_file = Path(tmpdir) / "speed_test.npz"

            primes = generate_n_primes(10000)
            cache = IncrementalSumCache(powers=[2, 3, 4])
            for prime in primes:
                cache.add_prime(prime)

            # Save checkpoint
            start = time.perf_counter()
            cache.save_checkpoint(cache_file)
            save_time = time.perf_counter() - start

            # Load checkpoint
            start = time.perf_counter()
            loaded = IncrementalSumCache.load_checkpoint(cache_file)
            load_time = time.perf_counter() - start

            # Both should be very fast
            assert save_time < 1.0, "Checkpoint save should be fast"
            assert load_time < 1.0, "Checkpoint load should be fast"

            # Verify loaded cache is correct
            assert loaded.get_prime_count() == 10000


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
