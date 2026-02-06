"""
types.py - Numeric type coercion and validation
================================================

Provides type coercion utilities for ensuring values fit within
expected numeric bounds, especially for external library compatibility.

Usage:
    from utils.types import _ensure_int, _ensure_uint64, _ensure_float32

    _ensure_int(7.0, "func")      # Returns 7 - integral float accepted
    _ensure_int(7.5, "func")      # Raises ValueError - non-integral rejected
    _ensure_uint64(n, "func")     # Validates for primesieve compatibility
    _ensure_float32(x, "func")    # Validates for GPU/cupy compatibility

Type Bounds:
    - int: Python arbitrary precision (unbounded)
    - int32: -2^31 to 2^31-1 (cupy)
    - int64: -2^63 to 2^63-1 (cupy)
    - uint64: 0 to 2^64-1 (primesieve)
    - float32: ±3.4e38, ~7 digits precision (cupy)
    - float64: ±1.8e308, ~15 digits precision (Python float)

Note:
    These utilities support Issue #20 (numeric type coercion) and
    Issue #37 (iterator dtype validation).
"""

from typing import Any, Union
import numpy as np

# Integer bounds for external libraries
INT32_MIN = -(2**31)
INT32_MAX = 2**31 - 1
INT64_MIN = -(2**63)
INT64_MAX = 2**63 - 1
UINT64_MAX = 2**64 - 1

# Float bounds (approximate - IEEE 754)
FLOAT32_MAX = 3.4028235e38
FLOAT64_MAX = 1.7976931348623157e308


def _ensure_int(value: Any, func_name: str) -> int:
    """
    Convert value to int if integral, otherwise raise appropriate error.

    Args:
        value: Value to convert (int, float, numpy integer)
        func_name: Function name for error messages

    Returns:
        Integer value

    Raises:
        ValueError: If float is not integral (e.g., 7.5)
        TypeError: If value is not a numeric type

    Examples:
        >>> _ensure_int(7, "test")
        7
        >>> _ensure_int(7.0, "test")
        7
        >>> _ensure_int(7.5, "test")
        ValueError: test() requires integral value, got 7.5
    """
    # Handle numpy integers
    if isinstance(value, np.integer):
        return int(value)

    # Handle floats - allow integral floats like 7.0
    if isinstance(value, float):
        if value != int(value):
            raise ValueError(f"{func_name}() requires integral value, got {value}")
        return int(value)

    # Handle regular ints
    if isinstance(value, int):
        return value

    # Reject other types
    raise TypeError(f"{func_name}() requires int, got {type(value).__name__}")


def _ensure_int32(value: Any, func_name: str) -> int:
    """
    Ensure value fits in 32-bit signed integer (for cupy int32).

    Args:
        value: Value to validate
        func_name: Function name for error messages

    Returns:
        Integer value within int32 bounds

    Raises:
        ValueError: If float is not integral
        TypeError: If value is not numeric
        OverflowError: If value exceeds int32 bounds

    Examples:
        >>> _ensure_int32(1000, "test")
        1000
        >>> _ensure_int32(2**31, "test")
        OverflowError: test() value 2147483648 exceeds int32 bounds
    """
    value = _ensure_int(value, func_name)
    if not (INT32_MIN <= value <= INT32_MAX):
        raise OverflowError(
            f"{func_name}() value {value} exceeds int32 bounds "
            f"[{INT32_MIN}, {INT32_MAX}]"
        )
    return value


def _ensure_int64(value: Any, func_name: str) -> int:
    """
    Ensure value fits in 64-bit signed integer (for cupy int64).

    Args:
        value: Value to validate
        func_name: Function name for error messages

    Returns:
        Integer value within int64 bounds

    Raises:
        ValueError: If float is not integral
        TypeError: If value is not numeric
        OverflowError: If value exceeds int64 bounds

    Examples:
        >>> _ensure_int64(10**18, "test")
        1000000000000000000
        >>> _ensure_int64(2**63, "test")
        OverflowError: test() value exceeds int64 bounds
    """
    value = _ensure_int(value, func_name)
    if not (INT64_MIN <= value <= INT64_MAX):
        raise OverflowError(
            f"{func_name}() value {value} exceeds int64 bounds "
            f"[{INT64_MIN}, {INT64_MAX}]"
        )
    return value


def _ensure_uint64(value: Any, func_name: str) -> int:
    """
    Ensure value fits in 64-bit unsigned integer (for primesieve).

    Args:
        value: Value to validate
        func_name: Function name for error messages

    Returns:
        Non-negative integer value within uint64 bounds

    Raises:
        ValueError: If float is not integral, or if value is negative
        TypeError: If value is not numeric
        OverflowError: If value exceeds uint64 bounds

    Examples:
        >>> _ensure_uint64(10**18, "test")
        1000000000000000000
        >>> _ensure_uint64(-1, "test")
        ValueError: test() requires non-negative integer, got -1
        >>> _ensure_uint64(2**64, "test")
        OverflowError: test() value exceeds uint64 bounds
    """
    value = _ensure_int(value, func_name)
    if value < 0:
        raise ValueError(f"{func_name}() requires non-negative integer, got {value}")
    if value > UINT64_MAX:
        raise OverflowError(
            f"{func_name}() value {value} exceeds uint64 bound {UINT64_MAX}"
        )
    return value


def _ensure_float(value: Any, func_name: str) -> float:
    """
    Convert value to float, accepting int, float, or numpy numeric types.

    Args:
        value: Value to convert
        func_name: Function name for error messages

    Returns:
        Float value

    Raises:
        TypeError: If value is not a numeric type

    Examples:
        >>> _ensure_float(7, "test")
        7.0
        >>> _ensure_float(3.14, "test")
        3.14
        >>> _ensure_float("3.14", "test")
        TypeError: test() requires numeric type, got str
    """
    if isinstance(value, (int, float, np.integer, np.floating)):
        return float(value)
    raise TypeError(f"{func_name}() requires numeric type, got {type(value).__name__}")


def _ensure_float32(value: Any, func_name: str) -> float:
    """
    Ensure value fits in 32-bit float (for cupy float32).

    Note: float32 has ~7 significant digits and range ±3.4e38.

    Args:
        value: Value to validate
        func_name: Function name for error messages

    Returns:
        Float value within float32 bounds

    Raises:
        TypeError: If value is not numeric
        OverflowError: If absolute value exceeds float32 bounds

    Examples:
        >>> _ensure_float32(3.14, "test")
        3.14
        >>> _ensure_float32(1e40, "test")
        OverflowError: test() value 1e+40 exceeds float32 bounds
    """
    f = _ensure_float(value, func_name)
    # Allow infinity and NaN to pass through
    if np.isfinite(f) and abs(f) > FLOAT32_MAX:
        raise OverflowError(
            f"{func_name}() value {value} exceeds float32 bounds (±{FLOAT32_MAX:.2e})"
        )
    return f


def _ensure_float64(value: Any, func_name: str) -> float:
    """
    Ensure value is valid 64-bit float (standard Python float).

    This is primarily for type checking - Python floats are already 64-bit.

    Args:
        value: Value to convert
        func_name: Function name for error messages

    Returns:
        Float value

    Raises:
        TypeError: If value is not numeric

    Examples:
        >>> _ensure_float64(3.14, "test")
        3.14
        >>> _ensure_float64(10**308, "test")
        1e+308
    """
    return _ensure_float(value, func_name)


def _ensure_positive(value: int, func_name: str) -> int:
    """
    Ensure integer value is positive (> 0).

    Args:
        value: Integer value to check
        func_name: Function name for error messages

    Returns:
        The value unchanged if positive

    Raises:
        ValueError: If value is not positive

    Examples:
        >>> _ensure_positive(5, "test")
        5
        >>> _ensure_positive(0, "test")
        ValueError: test() requires positive value, got 0
    """
    if value <= 0:
        raise ValueError(f"{func_name}() requires positive value, got {value}")
    return value


def _ensure_non_negative(value: int, func_name: str) -> int:
    """
    Ensure integer value is non-negative (>= 0).

    Args:
        value: Integer value to check
        func_name: Function name for error messages

    Returns:
        The value unchanged if non-negative

    Raises:
        ValueError: If value is negative

    Examples:
        >>> _ensure_non_negative(0, "test")
        0
        >>> _ensure_non_negative(-1, "test")
        ValueError: test() requires non-negative value, got -1
    """
    if value < 0:
        raise ValueError(f"{func_name}() requires non-negative value, got {value}")
    return value
