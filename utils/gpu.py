"""
gpu.py - GPU acceleration utilities for Prime-Square-Sum
==========================================================

Provides CuPy-based GPU computation for summing prime powers.
Falls back to CPU multiprocessing if GPU is unavailable.

Usage:
    from utils.gpu import init_gpu, gpu_power_sum, GPU_AVAILABLE

    if init_gpu():
        result = gpu_power_sum(primes, power=2)
    else:
        result = cpu_power_sum(primes, power=2)
"""

import numpy as np
from typing import Optional, Dict, Any
from multiprocessing import Pool, cpu_count

# Lazy import - don't crash if CuPy not installed
_cp = None
GPU_AVAILABLE = False
GPU_INFO: Optional[Dict[str, Any]] = None


def init_gpu() -> bool:
    """
    Initialize GPU support. Call once at startup.

    Returns:
        True if GPU is available and working, False otherwise.
    """
    global _cp, GPU_AVAILABLE, GPU_INFO

    try:
        import cupy as cp
        _cp = cp

        # Test GPU availability
        device_count = cp.cuda.runtime.getDeviceCount()
        if device_count == 0:
            GPU_AVAILABLE = False
            return False

        # Get device info
        props = cp.cuda.runtime.getDeviceProperties(0)
        mem_free, mem_total = cp.cuda.runtime.memGetInfo()

        GPU_INFO = {
            'name': props['name'].decode() if isinstance(props['name'], bytes) else props['name'],
            'device_count': device_count,
            'total_memory': mem_total,
            'free_memory': mem_free,
            'compute_capability': (props['major'], props['minor']),
        }

        # Warm up GPU with small test
        test = cp.array([1, 2, 3], dtype=cp.int64)
        _ = int(cp.sum(test ** 2))
        del test

        GPU_AVAILABLE = True
        return True

    except ImportError:
        GPU_AVAILABLE = False
        GPU_INFO = None
        return False
    except Exception as e:
        GPU_AVAILABLE = False
        GPU_INFO = {'error': str(e)}
        return False


def get_gpu_info() -> Optional[Dict[str, Any]]:
    """
    Get GPU device information.

    Returns:
        Dict with GPU info, or None if GPU not available.
    """
    if not GPU_AVAILABLE:
        return None
    return GPU_INFO


def print_gpu_status():
    """Print GPU status to console."""
    if GPU_AVAILABLE and GPU_INFO:
        print(f"GPU: {GPU_INFO['name']}")
        print(f"  Memory: {GPU_INFO['free_memory']/1e9:.1f} GB free / {GPU_INFO['total_memory']/1e9:.1f} GB total")
        print(f"  Compute: {GPU_INFO['compute_capability'][0]}.{GPU_INFO['compute_capability'][1]}")
    else:
        print("GPU: Not available")
        if GPU_INFO and 'error' in GPU_INFO:
            print(f"  Error: {GPU_INFO['error']}")


INT64_MAX = 9_223_372_036_854_775_807
MIN_CHUNK_SIZE = 100  # Below this, GPU overhead exceeds benefit


def _max_prime_for_power(power: int) -> int:
    """Return the largest prime where p^power fits in int64."""
    return int(INT64_MAX ** (1.0 / power))


def _find_int64_cutoff_index(primes: np.ndarray, power: int) -> int:
    """
    Find the index where p^power would exceed INT64_MAX.

    All primes before this index can have their powers computed on GPU.
    Primes at and after this index must use CPU.

    Args:
        primes: Sorted numpy array of primes
        power: Exponent to raise primes to

    Returns:
        Index of first prime that would overflow (or len(primes) if all fit)
    """
    max_prime = _max_prime_for_power(power)
    # Binary search for the cutoff point
    return int(np.searchsorted(primes, max_prime, side='right'))


def _calculate_safe_chunk_size(max_prime: int, power: int) -> int:
    """
    Calculate maximum chunk size that won't overflow int64 during GPU sum.

    Constraint: chunk_size × max_prime^power < INT64_MAX
    """
    max_value = int(max_prime) ** power
    if max_value >= INT64_MAX:
        return 0  # Single value overflows - GPU not usable
    return INT64_MAX // max_value


def gpu_power_values(primes: np.ndarray, power: int = 2,
                     batch_size: int = 100000) -> int:
    """
    GPU-accelerated exponentiation with CPU summing.

    Computes p^power on GPU (parallel exponentiation) but returns values
    to CPU for arbitrary-precision summing. Use when individual p^power
    values fit in int64 but sums would overflow.

    Args:
        primes: NumPy array of primes (int64)
        power: Exponent to raise each prime to
        batch_size: Process in batches to manage GPU memory (default: 100K)

    Returns:
        Sum of p^power for all primes (Python int for arbitrary precision)

    Raises:
        RuntimeError: If GPU is not available
    """
    if not GPU_AVAILABLE:
        raise RuntimeError("GPU not available. Call init_gpu() first or use cpu_power_sum().")

    total = 0  # Python int for arbitrary precision

    for i in range(0, len(primes), batch_size):
        batch = primes[i:i + batch_size]

        # Transfer to GPU
        primes_gpu = _cp.asarray(batch, dtype=_cp.int64)

        # Compute on GPU (massively parallel exponentiation)
        powered = primes_gpu ** power

        # Transfer back to CPU as NumPy array
        powered_cpu = _cp.asnumpy(powered)

        # Use Python's built-in sum with object dtype to get arbitrary precision
        # This converts int64 to Python int during accumulation, avoiding overflow
        batch_sum = int(np.sum(powered_cpu, dtype=object))

        total += batch_sum

        # Free GPU memory
        del primes_gpu, powered, powered_cpu
        _cp.get_default_memory_pool().free_all_blocks()

    return total


def gpu_power_sum(primes: np.ndarray, power: int = 2,
                  chunk_size: int = None) -> int:
    """
    GPU-accelerated sum of primes raised to a power.

    Args:
        primes: NumPy array of primes (int64)
        power: Exponent to raise each prime to (default: 2 for squares)
        chunk_size: Process in chunks to prevent int64 overflow in partial sums.
                    If None, automatically calculated based on max prime value.

    Returns:
        Sum of p^power for all primes (Python int for arbitrary precision)

    Raises:
        RuntimeError: If GPU is not available or chunk_size too small
    """
    if not GPU_AVAILABLE:
        raise RuntimeError("GPU not available. Call init_gpu() first or use cpu_power_sum().")

    # Auto-calculate safe chunk size based on actual max prime
    if chunk_size is None:
        max_prime = int(primes[-1]) if len(primes) > 0 else 2
        chunk_size = _calculate_safe_chunk_size(max_prime, power)

        if chunk_size < MIN_CHUNK_SIZE:
            raise RuntimeError(
                f"GPU overflow: max_prime^{power} exceeds int64. Use cpu_power_sum() instead."
            )

    total = 0  # Python int for arbitrary precision

    for i in range(0, len(primes), chunk_size):
        chunk = primes[i:i + chunk_size]

        # Transfer to GPU
        primes_gpu = _cp.asarray(chunk, dtype=_cp.int64)

        # Compute on GPU (massively parallel)
        powered = primes_gpu ** power

        # Sum on GPU (parallel reduction)
        partial_sum = int(_cp.sum(powered))

        # Accumulate with arbitrary precision
        total += partial_sum

        # Free GPU memory
        del primes_gpu, powered
        _cp.get_default_memory_pool().free_all_blocks()

    return total


def _cpu_power_chunk(args):
    """Process a chunk of primes - must be module-level for multiprocessing pickle."""
    chunk, power = args
    return sum(int(p) ** power for p in chunk)


def cpu_power_sum(primes: np.ndarray, power: int = 2,
                  num_workers: Optional[int] = None) -> int:
    """
    CPU multiprocessing sum of primes raised to a power.

    Args:
        primes: NumPy array of primes
        power: Exponent to raise each prime to (default: 2)
        num_workers: Number of worker processes (default: CPU count)

    Returns:
        Sum of p^power for all primes (Python int for arbitrary precision)
    """
    if num_workers is None:
        num_workers = cpu_count()

    # For small arrays, don't bother with parallelism
    if len(primes) < 10000:
        return sum(int(p) ** power for p in primes)

    # Split into chunks
    chunks = np.array_split(primes, num_workers)

    # Create args for each chunk (chunk, power)
    chunk_args = [(chunk, power) for chunk in chunks]

    with Pool(processes=num_workers) as pool:
        partial_sums = pool.map(_cpu_power_chunk, chunk_args)

    return sum(partial_sums)


MIN_GPU_SEGMENT = 1000  # Minimum primes to bother with GPU


def power_sum(primes: np.ndarray, power: int = 2,
              use_gpu: bool = True, **kwargs) -> int:
    """
    Compute sum of primes raised to a power, using GPU if available.

    This is the main entry point - it automatically chooses GPU or CPU.
    Uses hybrid approach: GPU for primes where p^power fits in int64,
    CPU for larger primes where overflow would occur.

    Args:
        primes: NumPy array of primes (must be sorted ascending)
        power: Exponent to raise each prime to (default: 2)
        use_gpu: Whether to use GPU if available (default: True)
        **kwargs: Additional arguments passed to gpu_power_sum or cpu_power_sum

    Returns:
        Sum of p^power for all primes
    """
    if not use_gpu or not GPU_AVAILABLE or len(primes) == 0:
        return cpu_power_sum(primes, power, **kwargs)

    # Find cutoff: primes before this index can use GPU
    cutoff = _find_int64_cutoff_index(primes, power)

    # Case 1: All primes fit in int64 individually
    if cutoff >= len(primes):
        max_prime = int(primes[-1])
        safe_chunk = _calculate_safe_chunk_size(max_prime, power)
        if safe_chunk >= MIN_CHUNK_SIZE:
            # Can do full GPU computation with chunked sums
            return gpu_power_sum(primes, power, **kwargs)
        else:
            # Individual values fit, but sums would overflow
            # Use GPU for exponentiation, CPU for summing
            return gpu_power_values(primes, power)

    # Case 2: No primes fit (or too few) - use CPU for everything
    if cutoff < MIN_GPU_SEGMENT:
        return cpu_power_sum(primes, power, **kwargs)

    # Case 3: Hybrid - GPU for small primes, CPU for large primes
    # For the GPU segment, individual values fit but sums may overflow
    # Use gpu_power_values for GPU exponentiation with CPU summing
    gpu_segment = primes[:cutoff]
    cpu_segment = primes[cutoff:]

    gpu_sum = gpu_power_values(gpu_segment, power)
    cpu_sum = cpu_power_sum(cpu_segment, power, **kwargs)

    return gpu_sum + cpu_sum


# Self-test
if __name__ == "__main__":
    print("=" * 50)
    print("GPU Utilities Self-Test")
    print("=" * 50)

    # Initialize GPU
    print("\nInitializing GPU...")
    if init_gpu():
        print_gpu_status()
    else:
        print("GPU not available, testing CPU fallback")

    # Test data
    test_primes = np.array([2, 3, 5, 7, 11, 13, 17], dtype=np.int64)
    expected_squared = 666  # 4 + 9 + 25 + 49 + 121 + 169 + 289

    print(f"\nTest primes: {test_primes.tolist()}")
    print(f"Expected sum of squares: {expected_squared}")

    # Test GPU
    if GPU_AVAILABLE:
        result = gpu_power_sum(test_primes, power=2)
        print(f"GPU result: {result} {'OK' if result == expected_squared else 'FAIL'}")

    # Test CPU
    result = cpu_power_sum(test_primes, power=2)
    print(f"CPU result: {result} {'OK' if result == expected_squared else 'FAIL'}")

    # Test unified interface
    result = power_sum(test_primes, power=2)
    print(f"Auto result: {result} {'OK' if result == expected_squared else 'FAIL'}")

    # Test different powers
    print("\nTesting different powers:")
    for p in [1, 2, 3]:
        result = power_sum(test_primes, power=p)
        manual = sum(int(x) ** p for x in test_primes)
        print(f"  power={p}: {result} {'OK' if result == manual else 'FAIL'}")

    print("\n" + "=" * 50)
    print("Self-test complete!")
