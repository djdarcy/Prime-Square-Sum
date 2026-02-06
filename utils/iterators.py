"""
iterators.py - Iterator classes for sequence enumeration
=========================================================

Provides iterator implementations for exploring mathematical sequences
with configurable start, stop, step, and numeric type bounds.

Usage:
    from utils.iterators import IntIterator, FloatIterator

    # Integer iteration
    for n in IntIterator(1, 100, step=1):
        print(n)  # 1, 2, 3, ..., 100

    # Float iteration with precision
    for x in FloatIterator(0.0, 1.0, step=0.1):
        print(x)  # 0.0, 0.1, 0.2, ..., 1.0

    # Linspace-style (compute step from count)
    for x in FloatIterator(0.0, 1.0, num_steps=11):
        print(x)  # 0.0, 0.1, 0.2, ..., 1.0

    # With dtype validation for external libraries
    for n in IntIterator(1, 1000000, dtype="uint64"):
        # Values validated for primesieve compatibility
        pass

Note:
    - FloatIterator uses decimal.Decimal internally to avoid precision issues
    - dtype parameter validates against external library bounds (primesieve, cupy)
    - See Issue #37 for iterator protocol design

Related Issues:
    - #20: Numeric type coercion
    - #24: Custom Iterator Functions (parent)
    - #37: Basic iterator protocol
    - #42: Multi-variable iteration strategies
"""

from abc import ABC, abstractmethod
from decimal import Decimal, ROUND_HALF_UP
from typing import Iterator, Union, Optional, Any

from utils.types import (
    _ensure_int,
    _ensure_int32,
    _ensure_int64,
    _ensure_uint64,
    _ensure_float,
    _ensure_float32,
    _ensure_float64,
)


class SequenceIterator(ABC):
    """
    Abstract base class for iteration over mathematical sequences.

    All iterator implementations must provide:
    - __iter__(): Return self, reset iteration state
    - __next__(): Return next value or raise StopIteration
    - current: Property to inspect current value without advancing

    Design for extensibility:
    - Subclasses can add custom step functions (#38)
    - Stateful iterators can maintain additional state (#39)
    - Strategies can wrap iterators for multi-variable control (#42)
    """

    @abstractmethod
    def __iter__(self) -> "SequenceIterator":
        """Reset and return iterator."""
        pass

    @abstractmethod
    def __next__(self) -> Any:
        """Return next value or raise StopIteration."""
        pass

    @property
    @abstractmethod
    def current(self) -> Any:
        """Current value (for inspection without advancing)."""
        pass

    @property
    @abstractmethod
    def exhausted(self) -> bool:
        """Whether iteration has completed."""
        pass


class IntIterator(SequenceIterator):
    """
    Integer iteration with configurable start, stop, step, and dtype.

    Args:
        start: Starting value (inclusive)
        stop: Ending value (inclusive)
        step: Step size (default 1, can be negative)
        dtype: Type for bounds validation:
            - "int": Python arbitrary precision (default, no bounds)
            - "int32": Validate for cupy int32 bounds
            - "int64": Validate for cupy int64 bounds
            - "uint64": Validate for primesieve bounds (non-negative)

    Examples:
        >>> list(IntIterator(1, 5))
        [1, 2, 3, 4, 5]

        >>> list(IntIterator(10, 0, step=-2))
        [10, 8, 6, 4, 2, 0]

        >>> list(IntIterator(1, 10, step=3))
        [1, 4, 7, 10]

        >>> it = IntIterator(1, 1000000, dtype="uint64")
        >>> # Values validated for primesieve compatibility

    Raises:
        ValueError: If step is zero, or dtype validation fails
        OverflowError: If values exceed dtype bounds
    """

    DTYPE_VALIDATORS = {
        "int": _ensure_int,
        "int32": _ensure_int32,
        "int64": _ensure_int64,
        "uint64": _ensure_uint64,
    }

    def __init__(
        self,
        start: int = 1,
        stop: int = 1000000,
        step: int = 1,
        dtype: str = "int",
    ):
        if step == 0:
            raise ValueError("IntIterator step cannot be zero")

        if dtype not in self.DTYPE_VALIDATORS:
            raise ValueError(
                f"IntIterator dtype must be one of {list(self.DTYPE_VALIDATORS.keys())}, "
                f"got '{dtype}'"
            )

        self._dtype = dtype
        self._validator = self.DTYPE_VALIDATORS[dtype]

        # Validate and store parameters
        self._start = self._validator(start, "IntIterator")
        self._stop = self._validator(stop, "IntIterator")
        self._step = _ensure_int(step, "IntIterator")

        # Iteration state
        self._current = self._start
        self._exhausted = False

        # Pre-check direction consistency
        if self._step > 0 and self._start > self._stop:
            self._exhausted = True  # Empty range
        elif self._step < 0 and self._start < self._stop:
            self._exhausted = True  # Empty range

    def __iter__(self) -> "IntIterator":
        """Reset and return iterator."""
        self._current = self._start
        self._exhausted = False

        # Re-check for empty range
        if self._step > 0 and self._start > self._stop:
            self._exhausted = True
        elif self._step < 0 and self._start < self._stop:
            self._exhausted = True

        return self

    def __next__(self) -> int:
        """Return next value or raise StopIteration."""
        if self._exhausted:
            raise StopIteration

        value = self._current

        # Check bounds before returning
        if self._step > 0:
            if value > self._stop:
                self._exhausted = True
                raise StopIteration
        else:  # step < 0
            if value < self._stop:
                self._exhausted = True
                raise StopIteration

        # Advance for next iteration
        next_value = self._current + self._step

        # Check if next value is within iteration bounds
        if self._step > 0:
            if next_value > self._stop:
                # Next value would exceed stop, mark exhausted
                self._exhausted = True
                return value
            # Validate next value for dtype bounds
            try:
                self._validator(next_value, "IntIterator")
            except (ValueError, OverflowError):
                # Next value would be invalid, mark exhausted after current
                self._exhausted = True
                return value
        else:  # step < 0
            if next_value < self._stop:
                # Next value would be below stop, mark exhausted
                self._exhausted = True
                return value
            # Validate next value for dtype bounds
            try:
                self._validator(next_value, "IntIterator")
            except (ValueError, OverflowError):
                self._exhausted = True
                return value

        self._current = next_value
        return value

    @property
    def current(self) -> int:
        """Current value (for inspection without advancing)."""
        return self._current

    @property
    def exhausted(self) -> bool:
        """Whether iteration has completed."""
        return self._exhausted

    @property
    def dtype(self) -> str:
        """The dtype used for validation."""
        return self._dtype

    def __repr__(self) -> str:
        return (
            f"IntIterator(start={self._start}, stop={self._stop}, "
            f"step={self._step}, dtype='{self._dtype}')"
        )


class FloatIterator(SequenceIterator):
    """
    Float iteration with precision control via decimal.Decimal.

    Supports two modes (mutually exclusive):
    1. step mode: Specify explicit step value
    2. num_steps mode: Specify number of steps, compute step automatically

    Args:
        start: Starting value (inclusive)
        stop: Ending value (inclusive)
        step: Explicit step size (mutually exclusive with num_steps)
        num_steps: Number of values to generate (mutually exclusive with step)
            Computes step = (stop - start) / (num_steps - 1)
        precision: Decimal places for rounding output (default 10)
        dtype: Type for bounds validation:
            - "float64": Python float / numpy float64 (default)
            - "float32": Validate for cupy float32 bounds

    Examples:
        >>> list(FloatIterator(0.0, 0.5, step=0.1))
        [0.0, 0.1, 0.2, 0.3, 0.4, 0.5]

        >>> list(FloatIterator(0.0, 1.0, num_steps=11))
        [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]

        >>> list(FloatIterator(1.0, 0.0, step=-0.25))
        [1.0, 0.75, 0.5, 0.25, 0.0]

    Note:
        Uses index-based calculation (start + i * step) to avoid
        floating-point accumulation errors.

    Raises:
        ValueError: If both step and num_steps are specified,
            or if neither is specified, or if step is zero
        OverflowError: If values exceed dtype bounds
    """

    DTYPE_VALIDATORS = {
        "float64": _ensure_float64,
        "float32": _ensure_float32,
    }

    def __init__(
        self,
        start: float = 0.0,
        stop: float = 1.0,
        step: Optional[float] = None,
        num_steps: Optional[int] = None,
        precision: int = 10,
        dtype: str = "float64",
    ):
        # Validate mutually exclusive parameters
        if step is None and num_steps is None:
            step = 0.1  # Default step
        elif step is not None and num_steps is not None:
            raise ValueError(
                "FloatIterator: cannot specify both 'step' and 'num_steps'"
            )

        if dtype not in self.DTYPE_VALIDATORS:
            raise ValueError(
                f"FloatIterator dtype must be one of {list(self.DTYPE_VALIDATORS.keys())}, "
                f"got '{dtype}'"
            )

        self._dtype = dtype
        self._validator = self.DTYPE_VALIDATORS[dtype]
        self._precision = precision

        # Convert to Decimal for precision
        self._start = Decimal(str(start))
        self._stop = Decimal(str(stop))

        # Compute step if num_steps specified
        if num_steps is not None:
            num_steps = _ensure_int(num_steps, "FloatIterator")
            if num_steps < 2:
                raise ValueError("FloatIterator num_steps must be at least 2")
            self._num_steps = num_steps
            self._step = (self._stop - self._start) / Decimal(num_steps - 1)
        else:
            if step == 0:
                raise ValueError("FloatIterator step cannot be zero")
            self._step = Decimal(str(step))
            # Compute num_steps for index-based iteration
            if self._step > 0:
                self._num_steps = int((self._stop - self._start) / self._step) + 1
            else:
                self._num_steps = int((self._start - self._stop) / abs(self._step)) + 1

        # Validate start/stop against dtype
        self._validator(float(self._start), "FloatIterator")
        self._validator(float(self._stop), "FloatIterator")

        # Iteration state (index-based to avoid accumulation errors)
        self._index = 0
        self._exhausted = False

        # Check for empty range
        if self._step > 0 and self._start > self._stop:
            self._exhausted = True
        elif self._step < 0 and self._start < self._stop:
            self._exhausted = True

    def __iter__(self) -> "FloatIterator":
        """Reset and return iterator."""
        self._index = 0
        self._exhausted = False

        if self._step > 0 and self._start > self._stop:
            self._exhausted = True
        elif self._step < 0 and self._start < self._stop:
            self._exhausted = True

        return self

    def __next__(self) -> float:
        """Return next value or raise StopIteration."""
        if self._exhausted:
            raise StopIteration

        # Index-based calculation avoids accumulation errors
        value_decimal = self._start + self._index * self._step

        # Check bounds
        if self._step > 0:
            if value_decimal > self._stop:
                self._exhausted = True
                raise StopIteration
        else:  # step < 0
            if value_decimal < self._stop:
                self._exhausted = True
                raise StopIteration

        # Convert to float with precision
        value = float(round(value_decimal, self._precision))

        # Validate against dtype
        try:
            self._validator(value, "FloatIterator")
        except OverflowError:
            self._exhausted = True
            raise StopIteration

        self._index += 1

        # Check if next value would exceed bounds, mark exhausted
        next_value_decimal = self._start + self._index * self._step
        if self._step > 0:
            if next_value_decimal > self._stop:
                self._exhausted = True
        else:  # step < 0
            if next_value_decimal < self._stop:
                self._exhausted = True

        return value

    @property
    def current(self) -> float:
        """Current value (for inspection without advancing)."""
        value_decimal = self._start + self._index * self._step
        return float(round(value_decimal, self._precision))

    @property
    def exhausted(self) -> bool:
        """Whether iteration has completed."""
        return self._exhausted

    @property
    def dtype(self) -> str:
        """The dtype used for validation."""
        return self._dtype

    def __repr__(self) -> str:
        return (
            f"FloatIterator(start={float(self._start)}, stop={float(self._stop)}, "
            f"step={float(self._step)}, precision={self._precision}, dtype='{self._dtype}')"
        )


def create_iterator(
    start: Union[int, float],
    stop: Union[int, float],
    step: Optional[Union[int, float]] = None,
    num_steps: Optional[int] = None,
    iter_type: str = "auto",
    dtype: Optional[str] = None,
    precision: int = 10,
) -> SequenceIterator:
    """
    Factory function to create appropriate iterator based on parameters.

    Args:
        start: Starting value
        stop: Ending value
        step: Step size (optional)
        num_steps: Number of steps (optional, for float)
        iter_type: "int", "float", or "auto" (detect from values)
        dtype: Type bounds validation (optional)
        precision: Decimal precision for float (default 10)

    Returns:
        IntIterator or FloatIterator instance

    Examples:
        >>> it = create_iterator(1, 100)  # Auto-detects int
        >>> it = create_iterator(0.0, 1.0, step=0.1)  # Auto-detects float
        >>> it = create_iterator(1, 1000, iter_type="int", dtype="uint64")
    """
    # Auto-detect type from values
    if iter_type == "auto":
        if isinstance(start, float) or isinstance(stop, float):
            iter_type = "float"
        elif step is not None and isinstance(step, float):
            iter_type = "float"
        else:
            iter_type = "int"

    if iter_type == "int":
        int_dtype = dtype or "int"
        int_step = step if step is not None else 1
        return IntIterator(
            start=int(start),
            stop=int(stop),
            step=int(int_step),
            dtype=int_dtype,
        )
    elif iter_type == "float":
        float_dtype = dtype or "float64"
        return FloatIterator(
            start=float(start),
            stop=float(stop),
            step=float(step) if step is not None else None,
            num_steps=num_steps,
            precision=precision,
            dtype=float_dtype,
        )
    else:
        raise ValueError(f"Unknown iter_type: {iter_type}")
