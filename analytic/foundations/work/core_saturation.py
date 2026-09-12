#!/usr/bin/env python3
"""Exact helpers for the D/X saturation lemma for 3-by-3 CP cores.

This module is intentionally small.  It uses :class:`fractions.Fraction`
only and checks algebraic identities used by the proof.  The finite tests in
``test_core_saturation.py`` are regression checks; the proof is the symbolic
argument recorded in ``outputs/R8_global_chart_coverage.md``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, Tuple


Q = Fraction
Matrix3 = Tuple[Tuple[Q, Q, Q], Tuple[Q, Q, Q], Tuple[Q, Q, Q]]


def _q(value) -> Q:
    return value if isinstance(value, Fraction) else Fraction(value)


@dataclass(frozen=True)
class CoreCoordinates:
    """Schur coordinates for a sign-normalized core.

    ``C = [[1,a,b], [c,c*a+r,c*b+s], [d,d*a+t,d*b+w]]``.
    """

    a: Q
    b: Q
    c: Q
    d: Q
    r: Q
    s: Q
    t: Q
    w: Q

    def __post_init__(self) -> None:
        for name in ("a", "b", "c", "d", "r", "s", "t", "w"):
            object.__setattr__(self, name, _q(getattr(self, name)))

    def reconstruct(self) -> Matrix3:
        return (
            (Q(1), self.a, self.b),
            (self.c, self.c * self.a + self.r, self.c * self.b + self.s),
            (self.d, self.d * self.a + self.t, self.d * self.b + self.w),
        )

    def is_sign_normalized_cp(self) -> bool:
        if not all(Q(0) <= z <= Q(1) for z in (self.a, self.b, self.c, self.d)):
            return False
        if not all(abs(z) <= 1 for row in self.reconstruct() for z in row):
            return False
        return all(abs(z) <= abs(self.r) for z in (self.s, self.t, self.w))

    def extended_final_pivot(self) -> Q:
        """Magnitude of the final pivot, continuously extended at ``r=0``."""

        if self.r == 0:
            if not all(z == 0 for z in (self.s, self.t, self.w)):
                raise ValueError("r=0 is incompatible with complete pivoting")
            return Q(0)
        return abs(self.w - self.t * self.s / self.r)

    def contract_middle(self, lam: Q, mu: Q) -> "CoreCoordinates":
        """Apply ``diag(1,lam,1) C diag(1,mu,1)`` exactly."""

        lam, mu = _q(lam), _q(mu)
        if not (0 <= lam <= 1 and 0 <= mu <= 1):
            raise ValueError("contraction factors must lie in [0,1]")
        return CoreCoordinates(
            mu * self.a,
            self.b,
            lam * self.c,
            self.d,
            lam * mu * self.r,
            lam * self.s,
            mu * self.t,
            self.w,
        )

    def transpose(self) -> "CoreCoordinates":
        """Transpose in Schur coordinates, without any symmetry quotient."""

        return CoreCoordinates(
            self.c, self.d, self.a, self.b,
            self.r, self.t, self.s, self.w,
        )


@dataclass(frozen=True)
class SaturationResult:
    branch: str
    lam: Q
    mu: Q
    core: CoreCoordinates

    def signs(self) -> Tuple[int, ...]:
        """Return the D or X chart signs when the saturated pivot is nonzero."""

        r = self.core.r
        if r == 0:
            raise ValueError("chart signs are non-unique at the zero tail")
        if self.branch == "D":
            return (1 if self.core.w == r else -1,)
        if self.branch == "X":
            return (
                1 if self.core.s == r else -1,
                1 if self.core.t == r else -1,
            )
        raise ValueError("unknown branch")


def saturate_core(core: CoreCoordinates) -> SaturationResult:
    """Construct the D/X contraction from the exact proof.

    The input must satisfy the fixed-order complete-pivoting inequalities.
    Positive-final-pivot inputs always produce a nonzero saturated ``r``.
    Zero-tail cases are retained only to make the construction total.
    """

    if not core.is_sign_normalized_cp():
        raise ValueError("input is not a sign-normalized CP core")

    if core.r == 0:
        # CP forces s=t=w=0.  Erasing the middle row puts the zero tail on D.
        out = core.contract_middle(Q(0), Q(1))
        return SaturationResult("D", Q(0), Q(1), out)

    sigma = abs(core.s / core.r)
    tau = abs(core.t / core.r)
    upsilon = abs(core.w / core.r)

    if upsilon >= sigma * tau:
        lam = max(tau, upsilon)
        if lam == 0:
            # Here t=w=0, hence the final pivot is zero.  This avoids 0/0.
            mu = Q(1)
        else:
            mu = upsilon / lam
        branch = "D"
    else:
        lam, mu = tau, sigma
        branch = "X"

    out = core.contract_middle(lam, mu)
    return SaturationResult(branch, lam, mu, out)


@dataclass(frozen=True)
class ClosedInterval:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        object.__setattr__(self, "lo", _q(self.lo))
        object.__setattr__(self, "hi", _q(self.hi))
        if self.lo > self.hi:
            raise ValueError("empty interval")

    def contains(self, value: Q) -> bool:
        value = _q(value)
        return self.lo <= value <= self.hi


@dataclass(frozen=True)
class CoreRootBox:
    """One closed axis-aligned D/X root box before exact domain filters."""

    chart: str
    signs: Tuple[int, ...]
    r_sign: int
    bounds: Dict[str, ClosedInterval]

    def contains(self, core: CoreCoordinates) -> bool:
        values = {
            "a": core.a,
            "b": core.b,
            "c": core.c,
            "d": core.d,
            "r": core.r,
            "s": core.s,
            "t": core.t,
            "w": core.w,
        }
        if not all(interval.contains(values[name]) for name, interval in self.bounds.items()):
            return False
        if self.chart == "D":
            return core.w == self.signs[0] * core.r
        if self.chart == "X":
            return core.s == self.signs[0] * core.r and core.t == self.signs[1] * core.r
        return False


def counterexample_core_root_boxes(alpha_lower: Q) -> Tuple[CoreRootBox, ...]:
    """Return the four D and eight X closed core roots.

    This uses the independently proved scalar bound ``p3,q <= 9/4``.  A
    counterexample to ``p3*q <= alpha`` has ``|r| > 2*alpha/9``.  Replacing
    alpha by a certified lower endpoint gives the closed over-cover here.
    """

    alpha_lower = _q(alpha_lower)
    eta = 2 * alpha_lower / 9
    if not (0 < eta < 1):
        raise ValueError("expected 0 < 2*alpha_lower/9 < 1")

    unit = ClosedInterval(0, 1)
    roots = []

    # D: w=eps_w*r.  If eps_w=-1, the individual sharp bounds
    # r,w in [-2,1] restrict r to [-1,1].
    for eps_w in (-1, 1):
        r_min = Q(-1) if eps_w == -1 else Q(-2)
        for r_sign in (-1, 1):
            r_box = (
                ClosedInterval(r_min, -eta)
                if r_sign == -1
                else ClosedInterval(eta, 1)
            )
            radius = max(abs(r_box.lo), abs(r_box.hi))
            tail_free = ClosedInterval(-radius, min(Q(1), radius))
            roots.append(
                CoreRootBox(
                    "D",
                    (eps_w,),
                    r_sign,
                    {
                        "a": unit, "b": unit, "c": unit, "d": unit,
                        "r": r_box, "s": tail_free, "t": tail_free,
                    },
                )
            )

    # X: s=eps_s*r and t=eps_t*r.  Any negative sign, together with the
    # individual sharp bounds r,s,t in [-2,1], restricts r to [-1,1].
    for eps_s in (-1, 1):
        for eps_t in (-1, 1):
            r_min = Q(-2) if eps_s == eps_t == 1 else Q(-1)
            for r_sign in (-1, 1):
                r_box = (
                    ClosedInterval(r_min, -eta)
                    if r_sign == -1
                    else ClosedInterval(eta, 1)
                )
                radius = max(abs(r_box.lo), abs(r_box.hi))
                w_box = ClosedInterval(-radius, min(Q(1), radius))
                roots.append(
                    CoreRootBox(
                        "X",
                        (eps_s, eps_t),
                        r_sign,
                        {
                            "a": unit, "b": unit, "c": unit, "d": unit,
                            "r": r_box, "w": w_box,
                        },
                    )
                )

    return tuple(roots)


def exact_domain_filter(core: CoreCoordinates, tau_lower: Q) -> bool:
    """The exact CP and high-tail filters applied inside a core root box."""

    tau_lower = _q(tau_lower)
    return core.is_sign_normalized_cp() and core.extended_final_pivot() >= tau_lower


def matrix_middle_contraction(C: Matrix3, lam: Q, mu: Q) -> Matrix3:
    """Direct matrix form, used only as an independent regression oracle."""

    row = (Q(1), _q(lam), Q(1))
    col = (Q(1), _q(mu), Q(1))
    return tuple(
        tuple(row[i] * C[i][j] * col[j] for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]
