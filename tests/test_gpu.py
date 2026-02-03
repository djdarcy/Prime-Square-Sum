"""
test_gpu.py - Unit tests for GPU acceleration
==============================================

Run with: python run_tests.py test_gpu
"""

import unittest
import numpy as np
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils import gpu as gpu_utils


# Test data
SMALL_PRIMES = np.array([2, 3, 5, 7, 11, 13, 17], dtype=np.int64)
EXPECTED_SUM_P1 = 58      # 2+3+5+7+11+13+17
EXPECTED_SUM_P2 = 666     # 4+9+25+49+121+169+289
EXPECTED_SUM_P3 = 8944    # 8+27+125+343+1331+2197+4913


class TestChunkSizeCalculation(unittest.TestCase):
    """Tests for _calculate_safe_chunk_size."""

    def test_power1_large_chunks(self):
        """Power=1 should allow very large chunks."""
        chunk = gpu_utils._calculate_safe_chunk_size(15_485_863, 1)
        self.assertGreater(chunk, 1_000_000)

    def test_power2_medium_chunks(self):
        """Power=2 should allow ~38k chunks for 1M primes."""
        chunk = gpu_utils._calculate_safe_chunk_size(15_485_863, 2)
        self.assertGreater(chunk, 30_000)
        self.assertLess(chunk, 50_000)

    def test_power3_no_safe_chunks(self):
        """Power=3 with large primes should return 0 (overflow)."""
        chunk = gpu_utils._calculate_safe_chunk_size(15_485_863, 3)
        self.assertEqual(chunk, 0)

    def test_small_primes_large_chunks(self):
        """Small primes should allow larger chunks even at high powers."""
        # Prime=17, power=3: 17^3 = 4913, plenty of room
        chunk = gpu_utils._calculate_safe_chunk_size(17, 3)
        self.assertGreater(chunk, 1_000_000)


class TestCPUPowerSum(unittest.TestCase):
    """Tests for cpu_power_sum (always works, reference implementation)."""

    def test_power1(self):
        result = gpu_utils.cpu_power_sum(SMALL_PRIMES, power=1)
        self.assertEqual(result, EXPECTED_SUM_P1)

    def test_power2(self):
        result = gpu_utils.cpu_power_sum(SMALL_PRIMES, power=2)
        self.assertEqual(result, EXPECTED_SUM_P2)

    def test_power3(self):
        result = gpu_utils.cpu_power_sum(SMALL_PRIMES, power=3)
        self.assertEqual(result, EXPECTED_SUM_P3)

    def test_empty_array(self):
        result = gpu_utils.cpu_power_sum(np.array([], dtype=np.int64), power=2)
        self.assertEqual(result, 0)


class TestGPUPowerSum(unittest.TestCase):
    """Tests for gpu_power_sum (requires GPU)."""

    @classmethod
    def setUpClass(cls):
        """Initialize GPU once for all tests in this class."""
        gpu_utils.init_gpu()
        cls.gpu_available = gpu_utils.GPU_AVAILABLE

    def test_power1(self):
        if not self.gpu_available:
            self.skipTest("GPU not available")
        result = gpu_utils.gpu_power_sum(SMALL_PRIMES, power=1)
        self.assertEqual(result, EXPECTED_SUM_P1)

    def test_power2(self):
        if not self.gpu_available:
            self.skipTest("GPU not available")
        result = gpu_utils.gpu_power_sum(SMALL_PRIMES, power=2)
        self.assertEqual(result, EXPECTED_SUM_P2)

    def test_power3_small_primes(self):
        """Power=3 works with small primes (no overflow)."""
        if not self.gpu_available:
            self.skipTest("GPU not available")
        result = gpu_utils.gpu_power_sum(SMALL_PRIMES, power=3)
        self.assertEqual(result, EXPECTED_SUM_P3)

    def test_overflow_raises_error(self):
        """Large primes at power=3 should raise RuntimeError."""
        if not self.gpu_available:
            self.skipTest("GPU not available")
        large_primes = np.array([15_485_863], dtype=np.int64)
        with self.assertRaises(RuntimeError):
            gpu_utils.gpu_power_sum(large_primes, power=3)


class TestPowerSum(unittest.TestCase):
    """Tests for power_sum (unified interface with auto-fallback)."""

    @classmethod
    def setUpClass(cls):
        """Initialize GPU once for all tests in this class."""
        gpu_utils.init_gpu()

    def test_power1(self):
        result = gpu_utils.power_sum(SMALL_PRIMES, power=1)
        self.assertEqual(result, EXPECTED_SUM_P1)

    def test_power2(self):
        result = gpu_utils.power_sum(SMALL_PRIMES, power=2)
        self.assertEqual(result, EXPECTED_SUM_P2)

    def test_power3(self):
        result = gpu_utils.power_sum(SMALL_PRIMES, power=3)
        self.assertEqual(result, EXPECTED_SUM_P3)

    def test_power4(self):
        """Higher powers should work via CPU fallback."""
        result = gpu_utils.power_sum(SMALL_PRIMES, power=4)
        expected = sum(int(p) ** 4 for p in SMALL_PRIMES)
        self.assertEqual(result, expected)

    def test_matches_cpu_reference(self):
        """power_sum should always match CPU reference for any power."""
        for power in range(1, 6):
            result = gpu_utils.power_sum(SMALL_PRIMES, power=power)
            expected = sum(int(p) ** power for p in SMALL_PRIMES)
            self.assertEqual(result, expected, f"Mismatch at power={power}")

    def test_disable_gpu(self):
        """use_gpu=False should force CPU path."""
        result = gpu_utils.power_sum(SMALL_PRIMES, power=2, use_gpu=False)
        self.assertEqual(result, EXPECTED_SUM_P2)


class TestIntegration(unittest.TestCase):
    """Integration tests with larger datasets."""

    @classmethod
    def setUpClass(cls):
        """Load test data and initialize GPU."""
        gpu_utils.init_gpu()
        cls.million_primes = None

        prime_file = "data/npy_files/1stmil.npy"
        if os.path.exists(prime_file):
            from utils.prime_io import load_primes
            cls.million_primes = load_primes(prime_file)

    def test_1m_primes_power2(self):
        """Verify GPU matches CPU for 1M primes at power=2."""
        if self.million_primes is None:
            self.skipTest("1M primes file not found")

        gpu_result = gpu_utils.power_sum(self.million_primes, power=2)
        cpu_result = gpu_utils.cpu_power_sum(self.million_primes, power=2)
        self.assertEqual(gpu_result, cpu_result)

    def test_1m_primes_power3(self):
        """Power=3 with 1M primes should fall back to CPU and work."""
        if self.million_primes is None:
            self.skipTest("1M primes file not found")

        # This should work via CPU fallback
        result = gpu_utils.power_sum(self.million_primes, power=3)
        # Verify against first 100 primes as sanity check
        partial = sum(int(p) ** 3 for p in self.million_primes[:100])
        self.assertGreater(result, partial)


if __name__ == "__main__":
    unittest.main()
