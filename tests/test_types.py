"""
Tests for utils/types.py - Numeric type coercion utilities.

Tests cover:
- Basic type conversion (_ensure_int, _ensure_float)
- Bounded integer types (int32, int64, uint64)
- Bounded float types (float32, float64)
- Edge cases (overflow, underflow, non-integral floats)
"""

import pytest
import numpy as np

from utils.types import (
    _ensure_int,
    _ensure_int32,
    _ensure_int64,
    _ensure_uint64,
    _ensure_float,
    _ensure_float32,
    _ensure_float64,
    _ensure_positive,
    _ensure_non_negative,
    INT32_MIN, INT32_MAX,
    INT64_MIN, INT64_MAX,
    UINT64_MAX,
    FLOAT32_MAX,
)


class TestEnsureInt:
    """Tests for _ensure_int()."""

    def test_native_int(self):
        """Native Python int passes through."""
        assert _ensure_int(7, "test") == 7
        assert _ensure_int(0, "test") == 0
        assert _ensure_int(-42, "test") == -42

    def test_integral_float(self):
        """Integral floats (7.0) are accepted and converted."""
        assert _ensure_int(7.0, "test") == 7
        assert _ensure_int(0.0, "test") == 0
        assert _ensure_int(-42.0, "test") == -42

    def test_non_integral_float_rejected(self):
        """Non-integral floats (7.5) raise ValueError."""
        with pytest.raises(ValueError, match="requires integral value"):
            _ensure_int(7.5, "test")
        with pytest.raises(ValueError, match="requires integral value"):
            _ensure_int(0.1, "test")
        with pytest.raises(ValueError, match="requires integral value"):
            _ensure_int(-3.14, "test")

    def test_numpy_int(self):
        """Numpy integer types are accepted."""
        assert _ensure_int(np.int32(7), "test") == 7
        assert _ensure_int(np.int64(7), "test") == 7
        assert _ensure_int(np.uint64(7), "test") == 7

    def test_non_numeric_rejected(self):
        """Non-numeric types raise TypeError."""
        with pytest.raises(TypeError, match="requires int, got str"):
            _ensure_int("7", "test")
        with pytest.raises(TypeError, match="requires int, got list"):
            _ensure_int([7], "test")
        with pytest.raises(TypeError, match="requires int, got NoneType"):
            _ensure_int(None, "test")

    def test_large_int(self):
        """Arbitrary precision integers work."""
        large = 10**100
        assert _ensure_int(large, "test") == large

    def test_func_name_in_error(self):
        """Function name appears in error message."""
        with pytest.raises(ValueError, match="myfunc\\(\\)"):
            _ensure_int(7.5, "myfunc")


class TestEnsureInt32:
    """Tests for _ensure_int32() - 32-bit signed integer bounds."""

    def test_within_bounds(self):
        """Values within int32 bounds pass."""
        assert _ensure_int32(0, "test") == 0
        assert _ensure_int32(1000, "test") == 1000
        assert _ensure_int32(-1000, "test") == -1000
        assert _ensure_int32(INT32_MAX, "test") == INT32_MAX
        assert _ensure_int32(INT32_MIN, "test") == INT32_MIN

    def test_overflow(self):
        """Values exceeding int32 max raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds int32 bounds"):
            _ensure_int32(INT32_MAX + 1, "test")
        with pytest.raises(OverflowError, match="exceeds int32 bounds"):
            _ensure_int32(2**31, "test")

    def test_underflow(self):
        """Values below int32 min raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds int32 bounds"):
            _ensure_int32(INT32_MIN - 1, "test")
        with pytest.raises(OverflowError, match="exceeds int32 bounds"):
            _ensure_int32(-(2**31) - 1, "test")


class TestEnsureInt64:
    """Tests for _ensure_int64() - 64-bit signed integer bounds."""

    def test_within_bounds(self):
        """Values within int64 bounds pass."""
        assert _ensure_int64(0, "test") == 0
        assert _ensure_int64(10**18, "test") == 10**18
        assert _ensure_int64(-(10**18), "test") == -(10**18)
        assert _ensure_int64(INT64_MAX, "test") == INT64_MAX
        assert _ensure_int64(INT64_MIN, "test") == INT64_MIN

    def test_overflow(self):
        """Values exceeding int64 max raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds int64 bounds"):
            _ensure_int64(INT64_MAX + 1, "test")
        with pytest.raises(OverflowError, match="exceeds int64 bounds"):
            _ensure_int64(2**63, "test")

    def test_underflow(self):
        """Values below int64 min raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds int64 bounds"):
            _ensure_int64(INT64_MIN - 1, "test")


class TestEnsureUint64:
    """Tests for _ensure_uint64() - 64-bit unsigned integer bounds (primesieve)."""

    def test_within_bounds(self):
        """Values within uint64 bounds pass."""
        assert _ensure_uint64(0, "test") == 0
        assert _ensure_uint64(1000, "test") == 1000
        assert _ensure_uint64(10**18, "test") == 10**18
        assert _ensure_uint64(UINT64_MAX, "test") == UINT64_MAX

    def test_negative_rejected(self):
        """Negative values raise ValueError (not OverflowError)."""
        with pytest.raises(ValueError, match="requires non-negative"):
            _ensure_uint64(-1, "test")
        with pytest.raises(ValueError, match="requires non-negative"):
            _ensure_uint64(-1000, "test")

    def test_overflow(self):
        """Values exceeding uint64 max raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds uint64 bound"):
            _ensure_uint64(UINT64_MAX + 1, "test")
        with pytest.raises(OverflowError, match="exceeds uint64 bound"):
            _ensure_uint64(2**64, "test")


class TestEnsureFloat:
    """Tests for _ensure_float()."""

    def test_native_float(self):
        """Native Python float passes through."""
        assert _ensure_float(3.14, "test") == 3.14
        assert _ensure_float(0.0, "test") == 0.0
        assert _ensure_float(-2.5, "test") == -2.5

    def test_int_converted(self):
        """Integers are converted to float."""
        assert _ensure_float(7, "test") == 7.0
        assert _ensure_float(0, "test") == 0.0

    def test_numpy_types(self):
        """Numpy numeric types are accepted."""
        assert _ensure_float(np.float32(3.14), "test") == pytest.approx(3.14, rel=1e-6)
        assert _ensure_float(np.float64(3.14), "test") == 3.14
        assert _ensure_float(np.int64(7), "test") == 7.0

    def test_non_numeric_rejected(self):
        """Non-numeric types raise TypeError."""
        with pytest.raises(TypeError, match="requires numeric type"):
            _ensure_float("3.14", "test")
        with pytest.raises(TypeError, match="requires numeric type"):
            _ensure_float(None, "test")


class TestEnsureFloat32:
    """Tests for _ensure_float32() - 32-bit float bounds (cupy)."""

    def test_within_bounds(self):
        """Values within float32 bounds pass."""
        assert _ensure_float32(0.0, "test") == 0.0
        assert _ensure_float32(3.14, "test") == 3.14
        assert _ensure_float32(1e30, "test") == 1e30
        assert _ensure_float32(-1e30, "test") == -1e30

    def test_overflow(self):
        """Values exceeding float32 max raise OverflowError."""
        with pytest.raises(OverflowError, match="exceeds float32 bounds"):
            _ensure_float32(1e40, "test")
        with pytest.raises(OverflowError, match="exceeds float32 bounds"):
            _ensure_float32(-1e40, "test")

    def test_infinity_allowed(self):
        """Infinity passes through (numpy allows inf in float32)."""
        assert _ensure_float32(float('inf'), "test") == float('inf')
        assert _ensure_float32(float('-inf'), "test") == float('-inf')

    def test_nan_allowed(self):
        """NaN passes through."""
        result = _ensure_float32(float('nan'), "test")
        assert np.isnan(result)


class TestEnsureFloat64:
    """Tests for _ensure_float64() - 64-bit float (standard Python)."""

    def test_basic(self):
        """Basic float64 validation."""
        assert _ensure_float64(3.14, "test") == 3.14
        assert _ensure_float64(1e308, "test") == 1e308

    def test_int_converted(self):
        """Integers converted to float."""
        assert _ensure_float64(7, "test") == 7.0


class TestEnsurePositive:
    """Tests for _ensure_positive()."""

    def test_positive_passes(self):
        """Positive values pass."""
        assert _ensure_positive(1, "test") == 1
        assert _ensure_positive(100, "test") == 100

    def test_zero_rejected(self):
        """Zero raises ValueError."""
        with pytest.raises(ValueError, match="requires positive value"):
            _ensure_positive(0, "test")

    def test_negative_rejected(self):
        """Negative values raise ValueError."""
        with pytest.raises(ValueError, match="requires positive value"):
            _ensure_positive(-1, "test")


class TestEnsureNonNegative:
    """Tests for _ensure_non_negative()."""

    def test_positive_passes(self):
        """Positive values pass."""
        assert _ensure_non_negative(1, "test") == 1

    def test_zero_passes(self):
        """Zero passes."""
        assert _ensure_non_negative(0, "test") == 0

    def test_negative_rejected(self):
        """Negative values raise ValueError."""
        with pytest.raises(ValueError, match="requires non-negative value"):
            _ensure_non_negative(-1, "test")


class TestTriangularFunctionValidation:
    """Tests that triangular functions now use type validation."""

    def test_tri_validates(self):
        """tri() rejects non-integral floats."""
        from utils.number_theory import tri

        assert tri(36) == 666
        assert tri(36.0) == 666  # Integral float OK
        with pytest.raises(ValueError, match="requires integral value"):
            tri(36.5)

    def test_qtri_validates(self):
        """qtri() rejects non-integral floats."""
        from utils.number_theory import qtri

        assert qtri(666) == 36
        assert qtri(666.0) == 36  # Integral float OK
        with pytest.raises(ValueError, match="requires integral value"):
            qtri(666.5)

    def test_trisum_validates(self):
        """trisum() rejects non-integral floats."""
        from utils.number_theory import trisum

        assert trisum(10) == 666
        assert trisum(10.0) == 666  # Integral float OK
        with pytest.raises(ValueError, match="requires integral value"):
            trisum(10.5)

    def test_is_triangular_validates(self):
        """is_triangular() rejects non-integral floats (via qtri)."""
        from utils.number_theory import is_triangular

        assert is_triangular(666) is True
        assert is_triangular(666.0) is True  # Integral float OK
        with pytest.raises(ValueError, match="requires integral value"):
            is_triangular(666.5)
