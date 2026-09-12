#!/usr/bin/env python3
"""Closed rational intervals with exact endpoint arithmetic.

This module deliberately uses :class:`fractions.Fraction` for every endpoint.
There is therefore no hidden binary floating-point rounding and no dependency
on a platform interval library.  Each arithmetic operation returns the
smallest closed interval obtainable from the usual endpoint formulas.

The class is intentionally small: it contains exactly the operations needed
by the circuit box certifier.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Union


RationalLike = Union[int, str, Fraction]


def as_fraction(value: RationalLike) -> Fraction:
    """Convert an integer, decimal/fraction string, or Fraction exactly.

    Floats are intentionally rejected.  Passing a decimal as a string, for
    example ``"0.125"``, records the intended rational number 1/8 rather than
    the exact value of a nearby binary float.
    """

    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        return Fraction(int(value))
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        return Fraction(value)
    raise TypeError("rational endpoints must be int, str, or Fraction; floats are forbidden")


@dataclass(frozen=True)
class RationalInterval:
    """A nonempty closed interval ``[lo, hi]`` with rational endpoints."""

    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        lo = as_fraction(self.lo)
        hi = as_fraction(self.hi)
        if lo > hi:
            raise ValueError("interval lower endpoint exceeds upper endpoint")
        object.__setattr__(self, "lo", lo)
        object.__setattr__(self, "hi", hi)

    @classmethod
    def point(cls, value: RationalLike) -> "RationalInterval":
        value = as_fraction(value)
        return cls(value, value)

    @classmethod
    def around(cls, center: RationalLike, radius: RationalLike) -> "RationalInterval":
        center = as_fraction(center)
        radius = as_fraction(radius)
        if radius < 0:
            raise ValueError("radius must be nonnegative")
        return cls(center - radius, center + radius)

    @property
    def is_point(self) -> bool:
        return self.lo == self.hi

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    @property
    def midpoint(self) -> Fraction:
        return (self.lo + self.hi) / 2

    def contains(self, value: RationalLike) -> bool:
        value = as_fraction(value)
        return self.lo <= value <= self.hi

    @property
    def contains_zero(self) -> bool:
        return self.lo <= 0 <= self.hi

    @property
    def abs_lower(self) -> Fraction:
        """The exact minimum of ``abs(x)`` over this interval."""

        if self.contains_zero:
            return Fraction(0)
        return min(abs(self.lo), abs(self.hi))

    @property
    def abs_upper(self) -> Fraction:
        """The exact maximum of ``abs(x)`` over this interval."""

        return max(abs(self.lo), abs(self.hi))

    def absolute(self) -> "RationalInterval":
        return RationalInterval(self.abs_lower, self.abs_upper)

    @staticmethod
    def _coerce(value: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        if isinstance(value, RationalInterval):
            return value
        return RationalInterval.point(value)

    def __neg__(self) -> "RationalInterval":
        return RationalInterval(-self.hi, -self.lo)

    def __add__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        other = self._coerce(other)
        return RationalInterval(self.lo + other.lo, self.hi + other.hi)

    def __radd__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        return self + other

    def __sub__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        other = self._coerce(other)
        return RationalInterval(self.lo - other.hi, self.hi - other.lo)

    def __rsub__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        return self._coerce(other) - self

    def __mul__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        other = self._coerce(other)
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return RationalInterval(min(products), max(products))

    def __rmul__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        return self * other

    def reciprocal(self) -> "RationalInterval":
        """Return ``1/self``; fail if the interval contains zero."""

        if self.contains_zero:
            raise ZeroDivisionError("cannot reciprocate an interval containing zero")
        endpoints = (1 / self.lo, 1 / self.hi)
        return RationalInterval(min(endpoints), max(endpoints))

    def __truediv__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        other = self._coerce(other)
        return self * other.reciprocal()

    def __rtruediv__(self, other: Union[RationalLike, "RationalInterval"]) -> "RationalInterval":
        return self._coerce(other) / self


ZERO = RationalInterval.point(0)
ONE = RationalInterval.point(1)

