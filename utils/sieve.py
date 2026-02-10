"""
sieve.py - Optimized prime generation with multiple algorithm strategies
=========================================================================

This module provides prime generation with automatic algorithm selection:

1. primesieve (if installed) - Fastest, C++ implementation
2. Basic sieve - O(n) memory, fast for small ranges
3. Segmented sieve - O(sqrt(n) + segment) memory, bounded for large ranges
4. Individual testing - O(primes found) memory, slowest but minimal memory

Algorithm selection follows precedence: CLI > config > auto-detection

Usage:
    from utils.sieve import generate_primes, nth_prime

    # Generate all primes up to 1 million (auto-selects best algorithm)
    primes = generate_primes(1_000_000)

    # Force specific algorithm
    primes = generate_primes(1_000_000, algorithm="segmented")

    # Get the 1000th prime
    p = nth_prime(1000)  # Returns 7919
"""

import numpy as np
from typing import List, Optional, Tuple
import warnings
import os

# Try to import primesieve (fast C++ implementation)
try:
    import primesieve
    PRIMESIEVE_AVAILABLE = True
except ImportError:
    PRIMESIEVE_AVAILABLE = False

# Try to import psutil for memory detection
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False

# Track if we've warned about primesieve (warn once per session)
_primesieve_warned = False

# Algorithm constants
ALGORITHM_AUTO = "auto"
ALGORITHM_PRIMESIEVE = "primesieve"
ALGORITHM_BASIC = "basic"
ALGORITHM_SEGMENTED = "segmented"
ALGORITHM_INDIVIDUAL = "individual"

VALID_ALGORITHMS = [
    ALGORITHM_AUTO,
    ALGORITHM_PRIMESIEVE,
    ALGORITHM_BASIC,
    ALGORITHM_SEGMENTED,
    ALGORITHM_INDIVIDUAL,
]

# Default segment size: 10MB (10 million bools)
DEFAULT_SEGMENT_SIZE = 10_000_000

# Minimum segment size: 1MB
MIN_SEGMENT_SIZE = 1_000_000

# Maximum segment size: 100MB
MAX_SEGMENT_SIZE = 100_000_000

# Module-level configuration (set by CLI/config)
_config = {
    "algorithm": ALGORITHM_AUTO,
    "max_memory_mb": None,
    "prefer": None,
}


def configure(algorithm: str = None, max_memory_mb: int = None,
              prefer: str = None) -> None:
    """
    Configure default sieve settings.

    Call this from CLI to set algorithm preferences before running queries.

    Args:
        algorithm: Default algorithm (e.g., "auto", "segmented", "basic")
        max_memory_mb: Maximum memory in MB
        prefer: Preference hint ("cpu", "memory", "minimal")
    """
    if algorithm is not None:
        if algorithm not in VALID_ALGORITHMS:
            raise ValueError(f"Invalid algorithm: {algorithm}")
        _config["algorithm"] = algorithm
    if max_memory_mb is not None:
        _config["max_memory_mb"] = max_memory_mb
    if prefer is not None:
        _config["prefer"] = prefer


def get_config() -> dict:
    """Return current sieve configuration."""
    return _config.copy()


def _warn_no_primesieve():
    """Warn once per session that primesieve is not available."""
    global _primesieve_warned
    if _primesieve_warned or os.environ.get('PRIME_SQUARE_SUM_QUIET'):
        return
    _primesieve_warned = True
    warnings.warn(
        "primesieve not available - using slower Python fallback.\n"
        "  Install: pip install primesieve\n"
        "     conda: conda install -c conda-forge python-primesieve\n"
        "  Silence: set PRIME_SQUARE_SUM_QUIET=1"
    )


def _get_available_memory_mb() -> int:
    """
    Get available system memory in MB.

    Returns conservative estimate if psutil unavailable.
    """
    if PSUTIL_AVAILABLE:
        try:
            available = psutil.virtual_memory().available
            return int(available / (1024 * 1024))
        except Exception:
            pass
    # Conservative fallback: assume 1GB available
    return 1024


def _calculate_segment_size(limit: int, max_memory_mb: Optional[int] = None) -> int:
    """
    Calculate optimal segment size based on memory constraints.

    Args:
        limit: Upper bound for sieve
        max_memory_mb: Optional memory limit in MB

    Returns:
        Segment size in number of elements
    """
    if max_memory_mb is None:
        # Use 10% of available memory, bounded by min/max
        available_mb = _get_available_memory_mb()
        max_memory_mb = max(1, int(available_mb * 0.1))

    # Convert MB to number of bool elements (1 byte each)
    segment_size = max_memory_mb * 1024 * 1024

    # Apply bounds
    segment_size = max(MIN_SEGMENT_SIZE, min(MAX_SEGMENT_SIZE, segment_size))

    # Don't exceed the limit itself
    segment_size = min(segment_size, limit)

    return segment_size


def _select_python_algorithm(limit: int, max_memory_mb: Optional[int] = None,
                              prefer: Optional[str] = None) -> str:
    """
    Select the best Python sieve algorithm based on constraints.

    Args:
        limit: Upper bound for sieve
        max_memory_mb: Optional memory limit in MB
        prefer: Optional preference hint ("memory", "minimal", "cpu")

    Returns:
        Algorithm name: "basic", "segmented", or "individual"
    """
    # Handle preference hints
    if prefer == "minimal":
        return ALGORITHM_INDIVIDUAL
    if prefer == "memory":
        # User wants fast even if memory-heavy - try basic first
        pass  # Fall through to memory check

    # Get available memory
    if max_memory_mb is None:
        available_mb = _get_available_memory_mb()
    else:
        available_mb = max_memory_mb

    # Memory needed for basic sieve (1 byte per element)
    needed_mb = limit / (1024 * 1024)

    # Use basic sieve if it fits in 40% of available memory
    if needed_mb <= available_mb * 0.4:
        return ALGORITHM_BASIC

    # Use segmented sieve if we have at least 10MB for segments
    if available_mb >= 10:
        return ALGORITHM_SEGMENTED

    # Last resort: individual testing
    return ALGORITHM_INDIVIDUAL


# =============================================================================
# Core Sieve Implementations
# =============================================================================

def _basic_sieve(limit: int) -> np.ndarray:
    """
    Basic Sieve of Eratosthenes with O(n) memory.

    Fast but requires memory proportional to limit.

    Args:
        limit: Upper bound (exclusive)

    Returns:
        numpy array of primes

    Complexity:
        Time: O(n log log n)
        Space: O(n)
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    # Boolean array: is_prime[i] = True if i is prime
    is_prime = np.ones(limit, dtype=bool)
    is_prime[0] = is_prime[1] = False

    # Sieve: only need to check up to sqrt(limit)
    for i in range(2, int(limit ** 0.5) + 1):
        if is_prime[i]:
            # Mark multiples of i as composite
            is_prime[i*i::i] = False

    # Extract primes
    return np.nonzero(is_prime)[0].astype(np.int64)


def _segmented_sieve(limit: int, segment_size: int = DEFAULT_SEGMENT_SIZE) -> np.ndarray:
    """
    Segmented Sieve of Eratosthenes with bounded memory.

    Processes the range in fixed-size segments, using only O(sqrt(n) + segment_size)
    memory regardless of limit.

    Args:
        limit: Upper bound (exclusive)
        segment_size: Size of each segment (number of elements)

    Returns:
        numpy array of primes

    Complexity:
        Time: O(n log log n) - same as basic sieve
        Space: O(sqrt(n) + segment_size) - bounded
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    sqrt_limit = int(limit ** 0.5) + 1

    # Step 1: Get small primes up to sqrt(limit) using basic sieve
    # These are needed to mark composites in all segments
    small_primes = _basic_sieve(sqrt_limit)

    # If limit <= sqrt_limit, we're done
    if limit <= sqrt_limit:
        return small_primes[small_primes < limit]

    # Step 2: Process range [sqrt_limit, limit) in segments
    all_primes = list(small_primes)

    low = sqrt_limit
    while low < limit:
        high = min(low + segment_size, limit)
        segment_length = high - low

        # Create segment array (all candidates start as prime)
        is_prime = np.ones(segment_length, dtype=bool)

        # Mark composites using small primes
        for p in small_primes:
            # Find first multiple of p >= low
            # We want the smallest k such that k*p >= low
            # k = ceil(low / p) = (low + p - 1) // p
            # But we start from p*p if p*p > low
            if p * p >= high:
                # This prime is too large to have multiples in this segment
                break

            # First multiple of p in this segment
            start = ((low + p - 1) // p) * p
            if start < p * p:
                start = p * p

            # Convert to segment-relative index
            start_idx = start - low

            if start_idx < segment_length:
                # Mark all multiples of p in this segment
                is_prime[start_idx::p] = False

        # Extract primes from this segment
        segment_primes = np.nonzero(is_prime)[0] + low
        all_primes.extend(segment_primes.tolist())

        low = high

    return np.array(all_primes, dtype=np.int64)


def _individual_sieve(limit: int) -> np.ndarray:
    """
    Individual primality testing with minimal memory.

    Tests each number individually using trial division with known primes.
    Uses pre-filter optimizations where available.

    Args:
        limit: Upper bound (exclusive)

    Returns:
        numpy array of primes

    Complexity:
        Time: O(n * sqrt(n) / log(n)) - slower than sieve
        Space: O(number of primes found) - minimal
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    if limit <= 2:
        return np.array([], dtype=np.int64)

    primes = [2]

    if limit <= 3:
        return np.array(primes, dtype=np.int64)

    primes.append(3)

    # Try to use pre-filter from number_theory if available
    try:
        from utils.number_theory import could_be_prime
        use_prefilter = True
    except ImportError:
        use_prefilter = False

    # Test odd numbers starting from 5
    for n in range(5, limit, 2):
        # Pre-filter check (digital root, etc.)
        if use_prefilter and not could_be_prime(n):
            continue

        # Trial division with known primes
        is_prime = True
        sqrt_n = int(n ** 0.5) + 1

        for p in primes:
            if p > sqrt_n:
                break
            if n % p == 0:
                is_prime = False
                break

        if is_prime:
            primes.append(n)

    return np.array(primes, dtype=np.int64)


# =============================================================================
# Facade / Dispatcher
# =============================================================================

def _python_sieve(limit: int, algorithm: str = ALGORITHM_AUTO,
                  max_memory_mb: Optional[int] = None,
                  prefer: Optional[str] = None) -> np.ndarray:
    """
    Facade for Python-based sieve implementations (Strategy Pattern).

    Dispatches to appropriate algorithm based on explicit selection
    or auto-detection from available memory and preferences.

    Args:
        limit: Upper bound (exclusive)
        algorithm: "auto", "basic", "segmented", or "individual"
        max_memory_mb: Optional memory limit in MB for auto-selection
        prefer: Optional preference hint ("memory", "minimal", "cpu")

    Returns:
        numpy array of primes

    Raises:
        ValueError: If unknown algorithm specified
    """
    _warn_no_primesieve()

    # Auto-select if needed
    if algorithm == ALGORITHM_AUTO:
        algorithm = _select_python_algorithm(limit, max_memory_mb, prefer)

    # Dispatch to specific implementation
    if algorithm == ALGORITHM_BASIC:
        return _basic_sieve(limit)
    elif algorithm == ALGORITHM_SEGMENTED:
        segment_size = _calculate_segment_size(limit, max_memory_mb)
        return _segmented_sieve(limit, segment_size)
    elif algorithm == ALGORITHM_INDIVIDUAL:
        return _individual_sieve(limit)
    else:
        raise ValueError(
            f"Unknown Python sieve algorithm: {algorithm}. "
            f"Valid options: {ALGORITHM_BASIC}, {ALGORITHM_SEGMENTED}, {ALGORITHM_INDIVIDUAL}"
        )


# =============================================================================
# Public API
# =============================================================================

def generate_primes(limit: int, algorithm: str = None,
                    max_memory_mb: Optional[int] = None,
                    prefer: Optional[str] = None) -> np.ndarray:
    """
    Generate all primes up to (but not including) limit.

    Args:
        limit: Upper bound (exclusive)
        algorithm: Algorithm to use (None uses configured default):
            - "auto": Select best available (default)
            - "primesieve": Use primesieve library (fastest)
            - "basic": Basic sieve, O(n) memory
            - "segmented": Segmented sieve, bounded memory
            - "individual": Individual testing, minimal memory
        max_memory_mb: Memory limit in MB (for auto-selection)
        prefer: Preference hint for auto-selection:
            - "cpu": Prefer CPU-intensive (primesieve/basic)
            - "memory": Prefer faster even if memory-heavy
            - "minimal": Prefer minimal memory usage

    Returns:
        numpy array of primes

    Raises:
        ValueError: If invalid algorithm or primesieve unavailable when requested

    Example:
        >>> generate_primes(20)
        array([2, 3, 5, 7, 11, 13, 17, 19])

        >>> generate_primes(1000000, algorithm="segmented")
        array([2, 3, 5, ..., 999961, 999979, 999983])
    """
    if limit < 2:
        return np.array([], dtype=np.int64)

    # Apply module-level config for defaults
    if algorithm is None:
        algorithm = _config.get("algorithm", ALGORITHM_AUTO)
    if max_memory_mb is None:
        max_memory_mb = _config.get("max_memory_mb")
    if prefer is None:
        prefer = _config.get("prefer")

    # Validate algorithm
    if algorithm not in VALID_ALGORITHMS:
        raise ValueError(
            f"Unknown algorithm: {algorithm}. "
            f"Valid options: {', '.join(VALID_ALGORITHMS)}"
        )

    # Handle explicit primesieve request
    if algorithm == ALGORITHM_PRIMESIEVE:
        if not PRIMESIEVE_AVAILABLE:
            raise ValueError(
                "primesieve requested but not installed.\n"
                "Install: pip install primesieve (Linux/Mac)\n"
                "         conda install -c conda-forge primesieve (Windows)"
            )
        return np.array(primesieve.primes(limit), dtype=np.int64)

    # Handle auto-selection
    if algorithm == ALGORITHM_AUTO:
        if PRIMESIEVE_AVAILABLE and prefer != "minimal":
            return np.array(primesieve.primes(limit), dtype=np.int64)
        else:
            return _python_sieve(limit, ALGORITHM_AUTO, max_memory_mb, prefer)

    # Handle explicit Python algorithm request
    return _python_sieve(limit, algorithm, max_memory_mb, prefer)


def generate_primes_range(start: int, stop: int, algorithm: str = ALGORITHM_AUTO,
                          max_memory_mb: Optional[int] = None) -> np.ndarray:
    """
    Generate all primes in range [start, stop).

    Args:
        start: Lower bound (inclusive)
        stop: Upper bound (exclusive)
        algorithm: Algorithm to use (see generate_primes)
        max_memory_mb: Memory limit in MB

    Returns:
        numpy array of primes in range
    """
    if algorithm == ALGORITHM_AUTO and PRIMESIEVE_AVAILABLE:
        primes = primesieve.primes(start, stop)
        return np.array(primes, dtype=np.int64)
    elif algorithm == ALGORITHM_PRIMESIEVE:
        if not PRIMESIEVE_AVAILABLE:
            raise ValueError("primesieve requested but not installed")
        primes = primesieve.primes(start, stop)
        return np.array(primes, dtype=np.int64)
    else:
        _warn_no_primesieve()
        # Fallback: generate all up to stop, then filter
        all_primes = _python_sieve(stop, algorithm, max_memory_mb)
        return all_primes[all_primes >= start]


def generate_n_primes(n: int, algorithm: str = ALGORITHM_AUTO,
                      max_memory_mb: Optional[int] = None) -> np.ndarray:
    """
    Generate the first n primes.

    Args:
        n: Number of primes to generate
        algorithm: Algorithm to use (see generate_primes)
        max_memory_mb: Memory limit in MB

    Returns:
        numpy array of first n primes

    Example:
        >>> generate_n_primes(7)
        array([2, 3, 5, 7, 11, 13, 17])
    """
    if n <= 0:
        return np.array([], dtype=np.int64)

    if algorithm == ALGORITHM_AUTO and PRIMESIEVE_AVAILABLE:
        primes = primesieve.n_primes(n)
        return np.array(primes, dtype=np.int64)
    elif algorithm == ALGORITHM_PRIMESIEVE:
        if not PRIMESIEVE_AVAILABLE:
            raise ValueError("primesieve requested but not installed")
        primes = primesieve.n_primes(n)
        return np.array(primes, dtype=np.int64)
    else:
        _warn_no_primesieve()
        # Estimate upper bound using prime number theorem
        # p_n ~ n * (ln(n) + ln(ln(n))) for n > 5
        import math
        if n < 6:
            limit = 15
        else:
            ln_n = math.log(n)
            limit = int(n * (ln_n + math.log(ln_n)) * 1.3)  # 1.3 safety factor

        primes = _python_sieve(limit, algorithm, max_memory_mb)
        while len(primes) < n:
            limit = int(limit * 1.5)
            primes = _python_sieve(limit, algorithm, max_memory_mb)

        return primes[:n]


def nth_prime(n: int, algorithm: str = ALGORITHM_AUTO) -> int:
    """
    Return the nth prime (1-indexed).

    Args:
        n: Which prime to return (1 = first prime = 2)
        algorithm: Algorithm to use (see generate_primes)

    Returns:
        The nth prime number

    Example:
        >>> nth_prime(7)
        17
        >>> nth_prime(1000)
        7919
    """
    if n <= 0:
        raise ValueError("n must be positive (1-indexed)")

    if algorithm == ALGORITHM_AUTO and PRIMESIEVE_AVAILABLE:
        return primesieve.nth_prime(n)
    elif algorithm == ALGORITHM_PRIMESIEVE:
        if not PRIMESIEVE_AVAILABLE:
            raise ValueError("primesieve requested but not installed")
        return primesieve.nth_prime(n)
    else:
        primes = generate_n_primes(n, algorithm)
        return int(primes[n - 1])


def prime_count(limit: int, algorithm: str = ALGORITHM_AUTO) -> int:
    """
    Count primes up to limit (prime counting function pi(x)).

    Args:
        limit: Upper bound
        algorithm: Algorithm to use (see generate_primes)

    Returns:
        Number of primes <= limit

    Example:
        >>> prime_count(100)
        25
    """
    if algorithm == ALGORITHM_AUTO and PRIMESIEVE_AVAILABLE:
        return primesieve.count_primes(limit)
    elif algorithm == ALGORITHM_PRIMESIEVE:
        if not PRIMESIEVE_AVAILABLE:
            raise ValueError("primesieve requested but not installed")
        return primesieve.count_primes(limit)
    else:
        return len(generate_primes(limit + 1, algorithm))


def get_available_algorithms() -> List[str]:
    """
    Return list of available sieve algorithms.

    Returns:
        List of algorithm names that can be used
    """
    available = [ALGORITHM_AUTO, ALGORITHM_BASIC, ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]
    if PRIMESIEVE_AVAILABLE:
        available.insert(1, ALGORITHM_PRIMESIEVE)
    return available


def get_algorithm_info() -> dict:
    """
    Return information about all sieve algorithms.

    Returns:
        Dictionary with algorithm details
    """
    return {
        ALGORITHM_AUTO: {
            "description": "Auto-select best available algorithm",
            "available": True,
        },
        ALGORITHM_PRIMESIEVE: {
            "description": "C++ primesieve library (fastest)",
            "available": PRIMESIEVE_AVAILABLE,
            "complexity_time": "O(n log log n)",
            "complexity_space": "O(sqrt(n)) internal",
        },
        ALGORITHM_BASIC: {
            "description": "Basic Sieve of Eratosthenes",
            "available": True,
            "complexity_time": "O(n log log n)",
            "complexity_space": "O(n)",
        },
        ALGORITHM_SEGMENTED: {
            "description": "Segmented sieve with bounded memory",
            "available": True,
            "complexity_time": "O(n log log n)",
            "complexity_space": "O(sqrt(n) + segment_size)",
        },
        ALGORITHM_INDIVIDUAL: {
            "description": "Individual testing (minimal memory)",
            "available": True,
            "complexity_time": "O(n * sqrt(n) / log(n))",
            "complexity_space": "O(primes found)",
        },
    }


# =============================================================================
# Quick Verification
# =============================================================================

if __name__ == "__main__":
    print(f"primesieve available: {PRIMESIEVE_AVAILABLE}")
    print(f"psutil available: {PSUTIL_AVAILABLE}")
    print(f"Available memory: {_get_available_memory_mb()} MB")
    print()

    print("Available algorithms:")
    for algo in get_available_algorithms():
        info = get_algorithm_info()[algo]
        status = "OK" if info["available"] else "NOT INSTALLED"
        print(f"  {algo}: {info['description']} [{status}]")
    print()

    # Test basic generation
    primes = generate_primes(100)
    print(f"Primes up to 100: {primes}")
    print(f"Count: {len(primes)}")
    print()

    # Test each algorithm
    print("Testing all algorithms produce same results:")
    limit = 10000
    expected = generate_primes(limit, algorithm=ALGORITHM_BASIC)

    for algo in [ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
        result = generate_primes(limit, algorithm=algo)
        match = np.array_equal(expected, result)
        print(f"  {algo}: {'MATCH' if match else 'MISMATCH'} ({len(result)} primes)")

    if PRIMESIEVE_AVAILABLE:
        result = generate_primes(limit, algorithm=ALGORITHM_PRIMESIEVE)
        match = np.array_equal(expected, result)
        print(f"  {ALGORITHM_PRIMESIEVE}: {'MATCH' if match else 'MISMATCH'} ({len(result)} primes)")
    print()

    # Test nth prime
    print(f"7th prime: {nth_prime(7)} (expected: 17)")
    print(f"1000th prime: {nth_prime(1000)} (expected: 7919)")
    print()

    # Test first n primes
    first_7 = generate_n_primes(7)
    print(f"First 7 primes: {first_7}")
    print(f"Sum of squares: {sum(p**2 for p in first_7)} (expected: 666)")
