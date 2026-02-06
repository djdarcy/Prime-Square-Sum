"""
Tests for utils/iterators.py - Iterator classes for sequence enumeration.

Tests cover:
- IntIterator basic iteration
- IntIterator negative steps
- IntIterator dtype validation
- FloatIterator with step
- FloatIterator with num_steps (linspace-style)
- FloatIterator precision
- FloatIterator dtype validation
- Edge cases (empty ranges, zero step, boundary values)
- create_iterator factory function
"""

import pytest
import numpy as np
from decimal import Decimal

from utils.iterators import (
    IntIterator,
    FloatIterator,
    SequenceIterator,
    create_iterator,
)
from utils.types import INT32_MAX, INT32_MIN, UINT64_MAX, FLOAT32_MAX


class TestIntIteratorBasic:
    """Tests for basic IntIterator functionality."""

    def test_simple_range(self):
        """Basic 1 to 5 iteration."""
        result = list(IntIterator(1, 5, 1))
        assert result == [1, 2, 3, 4, 5]

    def test_larger_range(self):
        """Larger range iteration."""
        result = list(IntIterator(1, 10, 1))
        assert result == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

    def test_step_of_two(self):
        """Step size of 2."""
        result = list(IntIterator(1, 10, 2))
        assert result == [1, 3, 5, 7, 9]

    def test_step_of_three(self):
        """Step size of 3."""
        result = list(IntIterator(1, 10, 3))
        assert result == [1, 4, 7, 10]

    def test_single_value(self):
        """Range with single value (start == stop)."""
        result = list(IntIterator(5, 5, 1))
        assert result == [5]

    def test_start_from_zero(self):
        """Range starting from zero."""
        result = list(IntIterator(0, 4, 1))
        assert result == [0, 1, 2, 3, 4]

    def test_negative_values(self):
        """Range with negative values."""
        result = list(IntIterator(-5, -1, 1))
        assert result == [-5, -4, -3, -2, -1]

    def test_crossing_zero(self):
        """Range crossing zero."""
        result = list(IntIterator(-2, 2, 1))
        assert result == [-2, -1, 0, 1, 2]


class TestIntIteratorNegativeStep:
    """Tests for IntIterator with negative steps (counting down)."""

    def test_countdown_basic(self):
        """Basic countdown."""
        result = list(IntIterator(5, 1, -1))
        assert result == [5, 4, 3, 2, 1]

    def test_countdown_step_two(self):
        """Countdown with step of -2."""
        result = list(IntIterator(10, 0, -2))
        assert result == [10, 8, 6, 4, 2, 0]

    def test_countdown_negative_range(self):
        """Countdown through negative numbers."""
        result = list(IntIterator(-1, -5, -1))
        assert result == [-1, -2, -3, -4, -5]

    def test_countdown_crossing_zero(self):
        """Countdown crossing zero."""
        result = list(IntIterator(2, -2, -1))
        assert result == [2, 1, 0, -1, -2]


class TestIntIteratorEmptyRanges:
    """Tests for empty range handling."""

    def test_empty_positive_step_reversed(self):
        """Positive step with start > stop yields empty."""
        result = list(IntIterator(5, 1, 1))
        assert result == []

    def test_empty_negative_step_reversed(self):
        """Negative step with start < stop yields empty."""
        result = list(IntIterator(1, 5, -1))
        assert result == []


class TestIntIteratorZeroStep:
    """Tests for zero step error handling."""

    def test_zero_step_raises(self):
        """Zero step raises ValueError."""
        with pytest.raises(ValueError, match="step cannot be zero"):
            IntIterator(1, 10, 0)


class TestIntIteratorDtype:
    """Tests for IntIterator dtype validation."""

    def test_dtype_int_default(self):
        """Default dtype is 'int' (unbounded)."""
        it = IntIterator(1, 10)
        assert it.dtype == "int"

    def test_dtype_int_large_value(self):
        """int dtype allows arbitrary precision."""
        large = 10**100
        it = IntIterator(large, large + 5, 1, dtype="int")
        result = list(it)
        assert result == [large, large + 1, large + 2, large + 3, large + 4, large + 5]

    def test_dtype_uint64_valid(self):
        """uint64 dtype accepts valid range."""
        it = IntIterator(0, 5, 1, dtype="uint64")
        result = list(it)
        assert result == [0, 1, 2, 3, 4, 5]

    def test_dtype_uint64_negative_start_raises(self):
        """uint64 dtype rejects negative start."""
        with pytest.raises(ValueError, match="requires non-negative"):
            IntIterator(-1, 10, 1, dtype="uint64")

    def test_dtype_uint64_overflow_raises(self):
        """uint64 dtype rejects values exceeding max."""
        with pytest.raises(OverflowError, match="exceeds uint64"):
            IntIterator(UINT64_MAX, UINT64_MAX + 10, 1, dtype="uint64")

    def test_dtype_int32_valid(self):
        """int32 dtype accepts valid range."""
        it = IntIterator(1, 100, 1, dtype="int32")
        result = list(it)
        assert len(result) == 100

    def test_dtype_int32_overflow_raises(self):
        """int32 dtype rejects values exceeding bounds."""
        with pytest.raises(OverflowError, match="exceeds int32"):
            IntIterator(INT32_MAX, INT32_MAX + 10, 1, dtype="int32")

    def test_dtype_int32_underflow_raises(self):
        """int32 dtype rejects values below min."""
        with pytest.raises(OverflowError, match="exceeds int32"):
            IntIterator(INT32_MIN - 10, INT32_MIN, 1, dtype="int32")

    def test_dtype_int64_valid(self):
        """int64 dtype accepts valid range."""
        it = IntIterator(1, 100, 1, dtype="int64")
        result = list(it)
        assert len(result) == 100

    def test_invalid_dtype_raises(self):
        """Invalid dtype raises ValueError."""
        with pytest.raises(ValueError, match="dtype must be one of"):
            IntIterator(1, 10, 1, dtype="invalid")


class TestIntIteratorProperties:
    """Tests for IntIterator properties."""

    def test_current_property(self):
        """current property returns current value."""
        it = IntIterator(1, 5, 1)
        assert it.current == 1
        next(it)
        assert it.current == 2

    def test_exhausted_property(self):
        """exhausted property tracks completion."""
        it = IntIterator(1, 2, 1)
        assert it.exhausted is False
        next(it)  # 1
        assert it.exhausted is False
        next(it)  # 2
        assert it.exhausted is True

    def test_repr(self):
        """__repr__ returns useful string."""
        it = IntIterator(1, 100, 5, dtype="uint64")
        repr_str = repr(it)
        assert "IntIterator" in repr_str
        assert "start=1" in repr_str
        assert "stop=100" in repr_str
        assert "step=5" in repr_str
        assert "uint64" in repr_str

    def test_reiter(self):
        """Iterator can be reset by calling __iter__."""
        it = IntIterator(1, 3, 1)
        assert list(it) == [1, 2, 3]
        assert list(it) == [1, 2, 3]  # Reset via __iter__


class TestFloatIteratorStep:
    """Tests for FloatIterator with explicit step."""

    def test_simple_step(self):
        """Basic float iteration with step."""
        result = list(FloatIterator(0.0, 0.5, step=0.1))
        assert len(result) == 6
        assert result[0] == pytest.approx(0.0)
        assert result[-1] == pytest.approx(0.5)

    def test_step_one_point_zero(self):
        """Float iteration with step=1.0."""
        result = list(FloatIterator(0.0, 5.0, step=1.0))
        assert result == [0.0, 1.0, 2.0, 3.0, 4.0, 5.0]

    def test_negative_step(self):
        """Float iteration counting down."""
        result = list(FloatIterator(1.0, 0.0, step=-0.25))
        assert len(result) == 5
        assert result[0] == pytest.approx(1.0)
        assert result[-1] == pytest.approx(0.0)

    def test_default_step(self):
        """Default step is 0.1."""
        result = list(FloatIterator(0.0, 0.3))
        assert len(result) == 4
        assert result == [pytest.approx(x) for x in [0.0, 0.1, 0.2, 0.3]]


class TestFloatIteratorNumSteps:
    """Tests for FloatIterator with num_steps (linspace-style)."""

    def test_num_steps_basic(self):
        """Linspace-style iteration."""
        result = list(FloatIterator(0.0, 1.0, num_steps=11))
        assert len(result) == 11
        assert result[0] == pytest.approx(0.0)
        assert result[5] == pytest.approx(0.5)
        assert result[-1] == pytest.approx(1.0)

    def test_num_steps_five(self):
        """Five evenly-spaced points."""
        result = list(FloatIterator(0.0, 1.0, num_steps=5))
        assert len(result) == 5
        expected = [0.0, 0.25, 0.5, 0.75, 1.0]
        for got, exp in zip(result, expected):
            assert got == pytest.approx(exp)

    def test_num_steps_two(self):
        """Minimum num_steps is 2."""
        result = list(FloatIterator(0.0, 10.0, num_steps=2))
        assert result == [pytest.approx(0.0), pytest.approx(10.0)]

    def test_num_steps_one_raises(self):
        """num_steps < 2 raises ValueError."""
        with pytest.raises(ValueError, match="num_steps must be at least 2"):
            FloatIterator(0.0, 1.0, num_steps=1)

    def test_num_steps_negative_range(self):
        """Linspace with start > stop."""
        result = list(FloatIterator(10.0, 0.0, num_steps=11))
        assert len(result) == 11
        assert result[0] == pytest.approx(10.0)
        assert result[-1] == pytest.approx(0.0)


class TestFloatIteratorMutualExclusion:
    """Tests for step/num_steps mutual exclusion."""

    def test_both_specified_raises(self):
        """Cannot specify both step and num_steps."""
        with pytest.raises(ValueError, match="cannot specify both"):
            FloatIterator(0.0, 1.0, step=0.1, num_steps=11)


class TestFloatIteratorZeroStep:
    """Tests for zero step handling."""

    def test_zero_step_raises(self):
        """Zero step raises ValueError."""
        with pytest.raises(ValueError, match="step cannot be zero"):
            FloatIterator(0.0, 1.0, step=0.0)


class TestFloatIteratorPrecision:
    """Tests for FloatIterator precision."""

    def test_avoids_accumulation_error(self):
        """Index-based calculation avoids floating-point accumulation."""
        # This would fail with naive addition: 0.1 + 0.1 + 0.1 != 0.3
        result = list(FloatIterator(0.0, 1.0, step=0.1))
        # Check that 0.3 is exactly correct (not 0.30000000000000004)
        assert result[3] == pytest.approx(0.3, abs=1e-10)
        assert result[6] == pytest.approx(0.6, abs=1e-10)
        assert result[9] == pytest.approx(0.9, abs=1e-10)

    def test_custom_precision(self):
        """Custom precision parameter."""
        # Lower precision rounds more aggressively
        result = list(FloatIterator(0.0, 1.0, step=0.1, precision=2))
        assert result[3] == pytest.approx(0.3, abs=1e-2)


class TestFloatIteratorDtype:
    """Tests for FloatIterator dtype validation."""

    def test_dtype_float64_default(self):
        """Default dtype is float64."""
        it = FloatIterator(0.0, 1.0, step=0.1)
        assert it.dtype == "float64"

    def test_dtype_float32_valid(self):
        """float32 dtype accepts valid range."""
        it = FloatIterator(0.0, 100.0, step=10.0, dtype="float32")
        result = list(it)
        assert len(result) == 11

    def test_dtype_float32_overflow_start(self):
        """float32 dtype rejects values exceeding bounds on start."""
        with pytest.raises(OverflowError, match="exceeds float32"):
            FloatIterator(1e40, 1e41, step=1e39, dtype="float32")

    def test_dtype_float32_overflow_stop(self):
        """float32 dtype rejects values exceeding bounds on stop."""
        with pytest.raises(OverflowError, match="exceeds float32"):
            FloatIterator(0.0, 1e40, step=1e39, dtype="float32")

    def test_invalid_dtype_raises(self):
        """Invalid dtype raises ValueError."""
        with pytest.raises(ValueError, match="dtype must be one of"):
            FloatIterator(0.0, 1.0, step=0.1, dtype="float16")


class TestFloatIteratorEmptyRanges:
    """Tests for empty range handling."""

    def test_empty_positive_step_reversed(self):
        """Positive step with start > stop yields empty."""
        result = list(FloatIterator(5.0, 1.0, step=0.5))
        assert result == []

    def test_empty_negative_step_reversed(self):
        """Negative step with start < stop yields empty."""
        result = list(FloatIterator(1.0, 5.0, step=-0.5))
        assert result == []


class TestFloatIteratorProperties:
    """Tests for FloatIterator properties."""

    def test_current_property(self):
        """current property returns current value."""
        it = FloatIterator(0.0, 1.0, step=0.5)
        assert it.current == pytest.approx(0.0)
        next(it)
        assert it.current == pytest.approx(0.5)

    def test_exhausted_property(self):
        """exhausted property tracks completion."""
        it = FloatIterator(0.0, 0.5, step=0.5)
        assert it.exhausted is False
        next(it)  # 0.0
        assert it.exhausted is False
        next(it)  # 0.5
        assert it.exhausted is True

    def test_repr(self):
        """__repr__ returns useful string."""
        it = FloatIterator(0.0, 1.0, step=0.1, precision=5, dtype="float32")
        repr_str = repr(it)
        assert "FloatIterator" in repr_str
        assert "start=0.0" in repr_str
        assert "stop=1.0" in repr_str
        assert "precision=5" in repr_str
        assert "float32" in repr_str

    def test_reiter(self):
        """Iterator can be reset by calling __iter__."""
        it = FloatIterator(0.0, 0.2, step=0.1)
        assert len(list(it)) == 3
        assert len(list(it)) == 3  # Reset via __iter__


class TestCreateIteratorFactory:
    """Tests for create_iterator() factory function."""

    def test_auto_detect_int(self):
        """Auto-detects integer type from int values."""
        it = create_iterator(1, 100)
        assert isinstance(it, IntIterator)
        result = list(it)
        assert result[0] == 1
        assert result[-1] == 100

    def test_auto_detect_float_from_start(self):
        """Auto-detects float type from float start."""
        it = create_iterator(0.0, 1.0, step=0.5)
        assert isinstance(it, FloatIterator)

    def test_auto_detect_float_from_stop(self):
        """Auto-detects float type from float stop."""
        it = create_iterator(0, 1.0, step=0.5)
        assert isinstance(it, FloatIterator)

    def test_auto_detect_float_from_step(self):
        """Auto-detects float type from float step."""
        it = create_iterator(0, 10, step=0.5)
        assert isinstance(it, FloatIterator)

    def test_explicit_int_type(self):
        """Explicit int type."""
        it = create_iterator(1.0, 10.0, iter_type="int")
        assert isinstance(it, IntIterator)

    def test_explicit_float_type(self):
        """Explicit float type."""
        it = create_iterator(1, 10, step=1, iter_type="float")
        assert isinstance(it, FloatIterator)

    def test_dtype_passthrough_int(self):
        """dtype passed to IntIterator."""
        it = create_iterator(1, 100, iter_type="int", dtype="uint64")
        assert it.dtype == "uint64"

    def test_dtype_passthrough_float(self):
        """dtype passed to FloatIterator."""
        it = create_iterator(0.0, 1.0, step=0.1, dtype="float32")
        assert it.dtype == "float32"

    def test_num_steps_passthrough(self):
        """num_steps passed to FloatIterator."""
        it = create_iterator(0.0, 1.0, num_steps=11)
        assert isinstance(it, FloatIterator)
        result = list(it)
        assert len(result) == 11

    def test_precision_passthrough(self):
        """precision passed to FloatIterator."""
        it = create_iterator(0.0, 1.0, step=0.1, iter_type="float", precision=5)
        assert isinstance(it, FloatIterator)

    def test_invalid_iter_type_raises(self):
        """Invalid iter_type raises ValueError."""
        with pytest.raises(ValueError, match="Unknown iter_type"):
            create_iterator(1, 10, iter_type="complex")


class TestSequenceIteratorABC:
    """Tests for SequenceIterator abstract base class."""

    def test_intiterator_is_sequence_iterator(self):
        """IntIterator is a SequenceIterator."""
        assert isinstance(IntIterator(1, 5), SequenceIterator)

    def test_floatiterator_is_sequence_iterator(self):
        """FloatIterator is a SequenceIterator."""
        assert isinstance(FloatIterator(0.0, 1.0, step=0.1), SequenceIterator)

    def test_cannot_instantiate_abc(self):
        """Cannot instantiate SequenceIterator directly."""
        with pytest.raises(TypeError):
            SequenceIterator()


class TestIntIteratorDtypeBoundaryBehavior:
    """Tests for dtype validation during iteration (not just at init)."""

    def test_uint64_iteration_to_max(self):
        """Iteration works correctly up to uint64 max."""
        # Start near max, iterate to max
        start = UINT64_MAX - 3
        it = IntIterator(start, UINT64_MAX, 1, dtype="uint64")
        result = list(it)
        # Should get 4 values: UINT64_MAX-3, -2, -1, UINT64_MAX
        assert len(result) == 4
        assert result[-1] == UINT64_MAX
        assert result[0] == UINT64_MAX - 3

    def test_int32_iteration_to_max(self):
        """Iteration works correctly up to int32 max."""
        start = INT32_MAX - 3
        it = IntIterator(start, INT32_MAX, 1, dtype="int32")
        result = list(it)
        assert len(result) == 4
        assert result[-1] == INT32_MAX

    def test_int32_iteration_to_min(self):
        """Iteration works correctly down to int32 min."""
        start = INT32_MIN + 3
        it = IntIterator(start, INT32_MIN, -1, dtype="int32")
        result = list(it)
        assert len(result) == 4
        assert result[-1] == INT32_MIN


class TestEdgeCases:
    """Additional edge case tests."""

    def test_large_step_skips_stop(self):
        """Large step that skips over stop."""
        result = list(IntIterator(1, 10, 7))
        assert result == [1, 8]

    def test_float_large_step_skips_stop(self):
        """Float large step that skips over stop."""
        result = list(FloatIterator(0.0, 1.0, step=0.7))
        assert len(result) == 2
        assert result[0] == pytest.approx(0.0)
        assert result[1] == pytest.approx(0.7)

    def test_numpy_int_input(self):
        """IntIterator accepts numpy integers."""
        it = IntIterator(np.int64(1), np.int64(5), np.int64(1))
        result = list(it)
        assert result == [1, 2, 3, 4, 5]

    def test_numpy_float_input(self):
        """FloatIterator accepts numpy floats."""
        it = FloatIterator(np.float64(0.0), np.float64(1.0), step=np.float64(0.5))
        result = list(it)
        assert len(result) == 3

    def test_integral_float_converted_for_int(self):
        """IntIterator accepts integral floats."""
        it = IntIterator(1.0, 5.0, 1.0)
        result = list(it)
        assert result == [1, 2, 3, 4, 5]
