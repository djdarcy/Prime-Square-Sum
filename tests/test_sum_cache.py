"""
test_sum_cache.py - Unit tests for IncrementalSumCache
======================================================

Tests incremental sum caching with focus on:
1. Correctness (incremental == batch)
2. Persistence (save/load)
3. Adaptive checkpointing
4. Arbitrary precision
5. Multi-power support
6. Migration from old format
"""

import pytest
import tempfile
from pathlib import Path
import json
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.sum_cache import IncrementalSumCache, CacheMetadata, migrate_old_checkpoint


class TestCacheMetadata:
    """Test CacheMetadata dataclass."""

    def test_metadata_defaults(self):
        """Test metadata initialization with defaults."""
        meta = CacheMetadata()
        assert meta.version == "1.0"
        assert meta.powers == [2, 3, 4]
        assert meta.prime_count == 0
        assert meta.last_prime is None
        assert meta.oeis_sequence_ids is None
        assert meta.created_timestamp > 0

    def test_metadata_custom(self):
        """Test metadata with custom values."""
        meta = CacheMetadata(powers=[2, 5], prime_count=100, last_prime=541)
        assert meta.powers == [2, 5]
        assert meta.prime_count == 100
        assert meta.last_prime == 541


class TestBasicAddition:
    """Test basic prime addition and retrieval."""

    def test_add_single_prime(self):
        """Test adding a single prime."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)

        assert cache.get_prime_count() == 1
        assert cache.get_last_prime() == 2
        assert cache.get_sum(2) == 4  # 2^2 = 4

    def test_add_multiple_primes(self):
        """Test adding multiple primes."""
        cache = IncrementalSumCache(powers=[2])

        # First 7 primes: 2, 3, 5, 7, 11, 13, 17
        primes = [2, 3, 5, 7, 11, 13, 17]
        for prime in primes:
            cache.add_prime(prime)

        # Sum of squares: 4 + 9 + 25 + 49 + 121 + 169 + 289 = 666
        assert cache.get_prime_count() == 7
        assert cache.get_last_prime() == 17
        assert cache.get_sum(2) == 666

    def test_multi_power_tracking(self):
        """Test tracking multiple powers simultaneously."""
        cache = IncrementalSumCache(powers=[2, 3])

        primes = [2, 3, 5]
        for prime in primes:
            cache.add_prime(prime)

        # Power 2: 4 + 9 + 25 = 38
        # Power 3: 8 + 27 + 125 = 160
        assert cache.get_sum(2) == 38
        assert cache.get_sum(3) == 160

    def test_get_nonexistent_power(self):
        """Test error when requesting non-tracked power."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)

        with pytest.raises(ValueError, match="not tracked"):
            cache.get_sum(3)


class TestCheckpointing:
    """Test checkpoint save and load functionality."""

    def test_checkpoint_save_load_cycle(self):
        """Test full checkpoint cycle: save and load."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_path = Path(tmpdir) / "test_cache.npz"

            # Create and populate cache
            cache1 = IncrementalSumCache(powers=[2, 3])
            primes = [2, 3, 5, 7, 11]
            for prime in primes:
                cache1.add_prime(prime)

            original_sum_p2 = cache1.get_sum(2)
            original_sum_p3 = cache1.get_sum(3)

            # Save checkpoint
            cache1.save_checkpoint(cache_path)

            # Load checkpoint
            cache2 = IncrementalSumCache.load_checkpoint(cache_path)

            # Verify loaded data matches original
            assert cache2.get_sum(2) == original_sum_p2
            assert cache2.get_sum(3) == original_sum_p3
            assert cache2.get_prime_count() == 5
            assert cache2.get_last_prime() == 11

    def test_checkpoint_creates_directory(self):
        """Test that checkpoint creation creates parent directories."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_path = Path(tmpdir) / "subdir" / "cache.npz"

            cache = IncrementalSumCache(powers=[2])
            cache.add_prime(2)
            cache.save_checkpoint(cache_path)

            assert cache_path.exists()
            assert cache_path.parent.exists()

    def test_load_nonexistent_checkpoint(self):
        """Test error when loading non-existent checkpoint."""
        with pytest.raises(FileNotFoundError):
            IncrementalSumCache.load_checkpoint(Path("/nonexistent/path.npz"))


class TestAdaptiveCheckpointing:
    """Test adaptive checkpoint intervals."""

    def test_should_checkpoint_below_10k(self):
        """Test checkpoint intervals for < 10K primes."""
        cache = IncrementalSumCache(powers=[2])

        # Add 999 primes - should not checkpoint yet
        for i in range(1, 1000):
            cache.add_prime(i)
            if i < 999:
                assert not cache.should_checkpoint()

        # 1000th prime - should checkpoint
        cache.add_prime(1000)
        assert cache.should_checkpoint()

    def test_should_checkpoint_10k_to_100k(self):
        """Test checkpoint intervals for 10K-100K primes."""
        cache = IncrementalSumCache(powers=[2])

        # Simulate being at 10K primes
        cache.metadata.prime_count = 10_000

        # Every 100 primes should checkpoint in this range
        for i in range(99):
            cache._checkpoint_counter += 1
            assert not cache.should_checkpoint()

        cache._checkpoint_counter += 1
        assert cache.should_checkpoint()

    def test_checkpoint_counter_resets(self):
        """Test that checkpoint counter resets after save."""
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_path = Path(tmpdir) / "cache.npz"
            cache = IncrementalSumCache(powers=[2])

            # Add primes
            for _ in range(1000):
                cache.add_prime(2)

            assert cache._checkpoint_counter == 1000
            assert cache.should_checkpoint()

            # Save checkpoint
            cache.save_checkpoint(cache_path)

            # Counter should reset
            assert cache._checkpoint_counter == 0
            assert not cache.should_checkpoint()


class TestArbitraryPrecision:
    """Test handling of large numbers (arbitrary precision)."""

    def test_large_prime_power(self):
        """Test computation with very large prime powers."""
        cache = IncrementalSumCache(powers=[10])

        # Use large prime
        large_prime = 1_000_000_007
        cache.add_prime(large_prime)

        result = cache.get_sum(10)

        # Verify it's the right value (large_prime^10)
        expected = large_prime ** 10
        assert result == expected

    def test_accumulated_large_sum(self):
        """Test that accumulated sums handle arbitrary precision."""
        cache = IncrementalSumCache(powers=[20])

        # Add several large primes and cube them
        large_primes = [1_000_000_007, 1_000_000_009, 1_000_000_021]
        for prime in large_primes:
            cache.add_prime(prime)

        result = cache.get_sum(20)

        # Should be sum of p^20
        expected = sum(p ** 20 for p in large_primes)
        assert result == expected
        assert isinstance(result, int)  # Python int can handle arbitrary size


class TestIncrementalVsBatch:
    """CRITICAL: Test that incremental equals batch computation."""

    def test_incremental_equals_batch_power_2(self):
        """CRITICAL: Verify incremental sum equals batch sum for power=2."""
        test_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

        # Batch computation
        batch_sum = sum(p ** 2 for p in test_primes)

        # Incremental computation
        cache = IncrementalSumCache(powers=[2])
        for prime in test_primes:
            cache.add_prime(prime)
        incremental_sum = cache.get_sum(2)

        # MUST be equal
        assert incremental_sum == batch_sum
        assert incremental_sum == 10466  # Sum of squares of first 15 primes

    def test_incremental_equals_batch_power_3(self):
        """CRITICAL: Verify incremental sum equals batch sum for power=3."""
        test_primes = [2, 3, 5, 7, 11, 13, 17]

        # Batch
        batch_sum = sum(p ** 3 for p in test_primes)

        # Incremental
        cache = IncrementalSumCache(powers=[3])
        for prime in test_primes:
            cache.add_prime(prime)
        incremental_sum = cache.get_sum(3)

        assert incremental_sum == batch_sum
        assert incremental_sum == 8944  # 8 + 27 + 125 + 343 + 1331 + 2197 + 4913 (including 19^3)

    def test_incremental_equals_batch_multi_power(self):
        """CRITICAL: Multi-power computation matches batch for each power."""
        test_primes = [2, 3, 5, 7, 11]

        # Batch
        batch_p2 = sum(p ** 2 for p in test_primes)
        batch_p3 = sum(p ** 3 for p in test_primes)
        batch_p4 = sum(p ** 4 for p in test_primes)

        # Incremental (computed simultaneously)
        cache = IncrementalSumCache(powers=[2, 3, 4])
        for prime in test_primes:
            cache.add_prime(prime)

        assert cache.get_sum(2) == batch_p2
        assert cache.get_sum(3) == batch_p3
        assert cache.get_sum(4) == batch_p4


class TestRollingWindow:
    """Test rolling window diagnostics."""

    def test_initial_values_tracked(self):
        """Test that first 2 primes are tracked."""
        cache = IncrementalSumCache(powers=[2])

        cache.add_prime(2)
        cache.add_prime(3)
        cache.add_prime(5)

        assert len(cache.initial_values) >= 2
        # First value should be (2, 4, 4, 0)
        assert cache.initial_values[0][0] == 2  # prime
        assert cache.initial_values[0][1] == 4  # 2^2
        assert cache.initial_values[0][2] == 4  # sum after first
        assert cache.initial_values[0][3] == 0  # count

    def test_recent_values_limited(self):
        """Test that recent values only keeps last 3."""
        cache = IncrementalSumCache(powers=[2])

        for i in range(1, 10):
            cache.add_prime(i)

        # Should only keep last 3
        assert len(cache.recent_values) <= 3


class TestMigration:
    """Test migration from old checkpoint format."""

    def test_migrate_old_checkpoint(self):
        """Test converting old JSON checkpoint to new .npz format."""
        with tempfile.TemporaryDirectory() as tmpdir:
            old_checkpoint_path = Path(tmpdir) / "checkpoint.json"
            new_cache_path = Path(tmpdir) / "cache.npz"

            # Create old format checkpoint (ComputationState)
            old_data = {
                "target": "666",
                "current_sum": "666",
                "primes_processed": 7,
                "last_prime": 17
            }

            with open(old_checkpoint_path, 'w') as f:
                json.dump(old_data, f)

            # Migrate
            migrate_old_checkpoint(old_checkpoint_path, new_cache_path)

            # Load and verify
            cache = IncrementalSumCache.load_checkpoint(new_cache_path)

            assert cache.get_prime_count() == 7
            assert cache.get_last_prime() == 17
            assert cache.get_sum(2) == 666
            # Note: only power=2 recovered (that's all old format had)

    def test_migrate_nonexistent_file(self):
        """Test error when migrating non-existent file."""
        with pytest.raises(FileNotFoundError):
            migrate_old_checkpoint(Path("/nonexistent.json"), Path("/tmp/out.npz"))


class TestEdgeCases:
    """Test edge cases and error conditions."""

    def test_empty_cache(self):
        """Test operations on empty cache."""
        cache = IncrementalSumCache(powers=[2])

        assert cache.get_prime_count() == 0
        assert cache.get_last_prime() is None
        assert cache.get_sum(2) == 0

    def test_single_prime(self):
        """Test cache with only one prime."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)

        assert cache.get_prime_count() == 1
        assert cache.get_sum(2) == 4

    def test_duplicate_primes(self):
        """Test adding duplicate primes (counts them both)."""
        cache = IncrementalSumCache(powers=[2])
        cache.add_prime(2)
        cache.add_prime(2)  # Add same prime again

        # Should sum both: 4 + 4 = 8
        assert cache.get_sum(2) == 8
        assert cache.get_prime_count() == 2

    def test_custom_powers(self):
        """Test cache with non-standard powers."""
        cache = IncrementalSumCache(powers=[5, 7, 11])

        cache.add_prime(2)
        assert cache.get_sum(5) == 32  # 2^5
        assert cache.get_sum(7) == 128  # 2^7
        assert cache.get_sum(11) == 2048  # 2^11


class TestReport:
    """Test diagnostic reporting."""

    def test_report_generation(self, capsys):
        """Test that report() produces output."""
        cache = IncrementalSumCache(powers=[2])

        cache.add_prime(2)
        cache.add_prime(3)
        cache.add_prime(5)

        cache.report()

        captured = capsys.readouterr()
        assert "IncrementalSumCache Report" in captured.out
        assert "Primes processed: 3" in captured.out
        assert "Last prime: 5" in captured.out


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
