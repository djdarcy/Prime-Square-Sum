"""
benchmark_gpu.py - GPU vs CPU performance comparison
=====================================================

Tests GPU acceleration performance against CPU baseline.
Run from project root: python tests/one-offs/performance/benchmark_gpu.py
"""

import time
import sys
import os

# Add project root to path (3 levels up from tests/one-offs/performance/)
PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))
sys.path.insert(0, PROJECT_ROOT)
os.chdir(PROJECT_ROOT)

from utils import gpu as gpu_utils
from utils.prime_io import load_primes


def benchmark_power_sum(primes, power=2):
    """Compare GPU vs CPU for sum of prime powers."""
    print(f"\n{len(primes):,} primes (power={power}):")
    print("-" * 40)

    # GPU timing - only for power=2 (power>2 overflows int64)
    if gpu_utils.GPU_AVAILABLE and power <= 2:
        start = time.perf_counter()
        gpu_result = gpu_utils.gpu_power_sum(primes, power=power)
        gpu_time = time.perf_counter() - start
        print(f"  GPU: {gpu_time:.3f}s")
    else:
        gpu_result = None
        gpu_time = None
        if power > 2:
            print("  GPU: Skipped (int64 overflow for power>2)")
        else:
            print("  GPU: Not available")

    # CPU single-threaded timing
    start = time.perf_counter()
    cpu_result = sum(int(p) ** power for p in primes)
    cpu_time = time.perf_counter() - start
    print(f"  CPU (single): {cpu_time:.3f}s")

    # CPU multiprocessing timing
    start = time.perf_counter()
    mp_result = gpu_utils.cpu_power_sum(primes, power=power)
    mp_time = time.perf_counter() - start
    print(f"  CPU (multi):  {mp_time:.3f}s")

    # Verify results match
    if gpu_result is not None:
        match = gpu_result == cpu_result == mp_result
        print(f"  Results match: {'OK' if match else 'FAIL'}")
        if gpu_time:
            print(f"  GPU speedup vs single: {cpu_time/gpu_time:.1f}x")
            print(f"  GPU speedup vs multi:  {mp_time/gpu_time:.1f}x")
    else:
        match = cpu_result == mp_result
        print(f"  CPU results match: {'OK' if match else 'FAIL'}")


def test_chunk_sizes(primes):
    """Test various chunk sizes to find optimal balance."""
    print("\nChunk size analysis (1M primes, power=2):")
    print("-" * 50)

    expected = sum(int(p) ** 2 for p in primes)

    for chunk_size in [1000, 5000, 10000, 25000, 40000, 50000]:
        start = time.perf_counter()
        result = gpu_utils.gpu_power_sum(primes, power=2, chunk_size=chunk_size)
        elapsed = time.perf_counter() - start
        status = "OK" if result == expected else "OVERFLOW"
        print(f"  chunk_size={chunk_size:>6}: {elapsed:.3f}s  [{status}]")


def main():
    print("=" * 50)
    print("GPU Benchmark - Prime Power Sums")
    print("=" * 50)

    # Initialize GPU
    print("\nInitializing GPU...")
    if gpu_utils.init_gpu():
        gpu_utils.print_gpu_status()
    else:
        print("GPU not available, running CPU-only benchmarks")

    # Load test data
    prime_file = "data/npy_files/1stmil.npy"
    if not os.path.exists(prime_file):
        print(f"\nError: {prime_file} not found")
        print("Download from GitHub Releases or generate with:")
        print("  from utils import generate_n_primes, save_primes")
        print("  save_primes(generate_n_primes(1_000_000), 'data/npy_files/1stmil.npy')")
        return

    primes = load_primes(prime_file)
    print(f"\nLoaded {len(primes):,} primes")

    # Run benchmarks
    benchmark_power_sum(primes, power=2)
    benchmark_power_sum(primes, power=3)

    if gpu_utils.GPU_AVAILABLE:
        test_chunk_sizes(primes)

    print("\n" + "=" * 50)
    print("Benchmark complete!")


if __name__ == "__main__":
    main()
