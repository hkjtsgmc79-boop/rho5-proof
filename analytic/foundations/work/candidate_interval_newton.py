#!/usr/bin/env python3
"""Certified rational Krawczyk isolation of the 5x5 candidate.

The square system is

    F = (P1, P2, P3, J),
    J = det(d(P1,P2,P3) / d(x,y,z)).

All certification arithmetic uses closed intervals with ``Fraction``
endpoints.  Floating/high-precision arithmetic is used only to find a good
centre; it is never trusted by the certificate.  In particular, the
preconditioner is the *exact rational inverse* of F'(m), and every Krawczyk
inclusion comparison is an exact comparison of integers.

The determinant J is deliberately not expanded.  Its interval value and
gradient are evaluated from first and second derivatives of P1,P2,P3 using
multilinearity of the determinant.  This avoids a 5059-term expanded J and
also gives a substantially tighter interval extension.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import sympy as sp

from rational_interval import RationalInterval as RI


ROOT = Path(__file__).resolve().parents[1]
POLY_PATHS = tuple(ROOT / "work" / "sympy_recompute" / f"p{i}.txt" for i in (1, 2, 3))
P5_PATH = ROOT / "outputs" / "P5_coefficients_ascending.csv"

VARIABLE_NAMES = ("x", "y", "z", "g")
X, Y, Z, G = sp.symbols("x y z g")
VARIABLES = (X, Y, Z, G)

# Exact, independently Sturm-certified interval from verify_p5_exact.py.
P5_LO_TEXT = (
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560269"
)
P5_HI_TEXT = (
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560270"
)

START = (
    "-0.6175326768818270947460429475716614",
    "-0.7791507422163110611449349424590389",
    "0.4532249098468374671837099599775295",
    "4.1325170786324728542233468532773713",
)


def decimal_fraction(text: str) -> Fraction:
    """Interpret a finite decimal string as the intended exact rational."""

    return Fraction(text)


def fraction_decimal(value: Fraction, digits: int = 20) -> str:
    """A diagnostic decimal, rounded by Decimal/mpmath only for display."""

    with mp.workdps(digits + 10):
        return mp.nstr(mp.mpf(value.numerator) / value.denominator, digits)


def terminating_decimal(value: Fraction) -> str:
    """Return the exact finite decimal expansion of a terminating rational."""

    numerator, denominator = value.numerator, value.denominator
    twos = fives = 0
    while denominator % 2 == 0:
        denominator //= 2
        twos += 1
    while denominator % 5 == 0:
        denominator //= 5
        fives += 1
    if denominator != 1:
        raise ValueError("rational has no finite decimal expansion")
    places = max(twos, fives)
    scaled = abs(numerator) * 2 ** (places - twos) * 5 ** (places - fives)
    digits = str(scaled).rjust(places + 1, "0")
    if places:
        digits = digits[:-places] + "." + digits[-places:]
    if numerator < 0:
        digits = "-" + digits
    return digits


@dataclass(frozen=True)
class SparsePolynomial:
    """Integer/rational sparse polynomial in (x,y,z,g)."""

    terms: tuple[tuple[tuple[int, int, int, int], Fraction], ...]

    @classmethod
    def from_sympy(cls, poly: sp.Poly) -> "SparsePolynomial":
        terms = []
        for monomial, coefficient in poly.terms():
            q = sp.Rational(coefficient)
            terms.append((tuple(int(e) for e in monomial), Fraction(int(q.p), int(q.q))))
        return cls(tuple(terms))

    @property
    def max_degrees(self) -> tuple[int, int, int, int]:
        if not self.terms:
            return (0, 0, 0, 0)
        return tuple(max(monomial[k] for monomial, _ in self.terms) for k in range(4))

    def evaluate_fraction(self, point: Sequence[Fraction]) -> Fraction:
        max_degrees = self.max_degrees
        powers: list[list[Fraction]] = []
        for value, degree in zip(point, max_degrees):
            row = [Fraction(1)]
            for _ in range(degree):
                row.append(row[-1] * value)
            powers.append(row)
        total = Fraction(0)
        for monomial, coefficient in self.terms:
            term = coefficient
            for k, exponent in enumerate(monomial):
                term *= powers[k][exponent]
            total += term
        return total

    def evaluate_interval(self, box: Sequence[RI]) -> RI:
        max_degrees = self.max_degrees
        powers: list[list[RI]] = []
        for value, degree in zip(box, max_degrees):
            row = [RI.point(1)]
            for _ in range(degree):
                row.append(row[-1] * value)
            powers.append(row)
        total = RI.point(0)
        for monomial, coefficient in self.terms:
            term = RI.point(coefficient)
            for k, exponent in enumerate(monomial):
                term = term * powers[k][exponent]
            total = total + term
        return total

    def evaluate_mp(self, point: Sequence[mp.mpf]) -> mp.mpf:
        max_degrees = self.max_degrees
        powers: list[list[mp.mpf]] = []
        for value, degree in zip(point, max_degrees):
            row = [mp.mpf(1)]
            for _ in range(degree):
                row.append(row[-1] * value)
            powers.append(row)
        total = mp.mpf(0)
        for monomial, coefficient in self.terms:
            term = mp.mpf(coefficient.numerator) / coefficient.denominator
            for k, exponent in enumerate(monomial):
                term *= powers[k][exponent]
            total += term
        return total


def det3(rows: Sequence[Sequence[object]]) -> object:
    """Three-by-three determinant over Fraction, RI, or mp.mpf."""

    a, b, c = rows
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


@dataclass
class CandidateSystem:
    p: tuple[SparsePolynomial, SparsePolynomial, SparsePolynomial]
    first: tuple[tuple[SparsePolynomial, ...], ...]
    second: tuple[tuple[tuple[SparsePolynomial, ...], ...], ...]

    @classmethod
    def load(cls) -> "CandidateSystem":
        local_dict = {name: symbol for name, symbol in zip(VARIABLE_NAMES, VARIABLES)}
        exprs = [sp.sympify(path.read_text(), locals=local_dict) for path in POLY_PATHS]
        polys = tuple(sp.Poly(expr, *VARIABLES, domain=sp.QQ) for expr in exprs)
        p = tuple(SparsePolynomial.from_sympy(poly) for poly in polys)
        first = tuple(
            tuple(SparsePolynomial.from_sympy(sp.Poly(sp.diff(expr, v), *VARIABLES, domain=sp.QQ)) for v in VARIABLES)
            for expr in exprs
        )
        second = tuple(
            tuple(
                tuple(
                    SparsePolynomial.from_sympy(
                        sp.Poly(sp.diff(expr, v, w), *VARIABLES, domain=sp.QQ)
                    )
                    for w in VARIABLES
                )
                for v in VARIABLES[:3]
            )
            for expr in exprs
        )
        return cls(p=p, first=first, second=second)

    def _evaluate(self, point: Sequence[object], method: str) -> tuple[list[object], list[list[object]]]:
        evaluate = lambda poly: getattr(poly, method)(point)
        p_values = [evaluate(poly) for poly in self.p]
        gradients = [[evaluate(self.first[i][k]) for k in range(4)] for i in range(3)]
        rows_xyz = [row[:3] for row in gradients]
        j_value = det3(rows_xyz)
        j_gradient = []
        for variable in range(4):
            derivative = None
            for equation in range(3):
                replaced = [list(row) for row in rows_xyz]
                replaced[equation] = [
                    evaluate(self.second[equation][xyz][variable]) for xyz in range(3)
                ]
                summand = det3(replaced)
                derivative = summand if derivative is None else derivative + summand
            j_gradient.append(derivative)
        return p_values + [j_value], gradients + [j_gradient]

    def evaluate_fraction(self, point: Sequence[Fraction]) -> tuple[list[Fraction], list[list[Fraction]]]:
        return self._evaluate(point, "evaluate_fraction")  # type: ignore[return-value]

    def evaluate_interval(self, box: Sequence[RI]) -> tuple[list[RI], list[list[RI]]]:
        return self._evaluate(box, "evaluate_interval")  # type: ignore[return-value]

    def evaluate_mp(self, point: Sequence[mp.mpf]) -> tuple[list[mp.mpf], list[list[mp.mpf]]]:
        return self._evaluate(point, "evaluate_mp")  # type: ignore[return-value]


def invert_fraction_matrix(matrix: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    """Exact Gauss-Jordan inverse, failing on a singular pivot."""

    n = len(matrix)
    augmented = [list(row) + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((row for row in range(col, n) if augmented[row][col] != 0), None)
        if pivot is None:
            raise ZeroDivisionError("singular rational matrix")
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        scale = augmented[col][col]
        augmented[col] = [value / scale for value in augmented[col]]
        for row in range(n):
            if row == col:
                continue
            scale = augmented[row][col]
            if scale:
                augmented[row] = [a - scale * b for a, b in zip(augmented[row], augmented[col])]
    return [row[n:] for row in augmented]


def matvec_fraction(matrix: Sequence[Sequence[Fraction]], vector: Sequence[Fraction]) -> list[Fraction]:
    return [sum((a * b for a, b in zip(row, vector)), Fraction(0)) for row in matrix]


def matmul_fraction_interval(
    left: Sequence[Sequence[Fraction]], right: Sequence[Sequence[RI]]
) -> list[list[RI]]:
    rows, inner, columns = len(left), len(right), len(right[0])
    return [
        [sum((RI.point(left[i][k]) * right[k][j] for k in range(inner)), RI.point(0)) for j in range(columns)]
        for i in range(rows)
    ]


def matvec_interval(matrix: Sequence[Sequence[RI]], vector: Sequence[RI]) -> list[RI]:
    return [sum((a * b for a, b in zip(row, vector)), RI.point(0)) for row in matrix]


def newton_seed(system: CandidateSystem, digits: int = 245) -> tuple[mp.mpf, ...]:
    """Untrusted high-precision Newton iteration used only to centre a box."""

    with mp.workdps(digits + 25):
        point = mp.matrix([mp.mpf(value) for value in START])
        threshold = mp.power(10, -(digits - 15))
        for _ in range(30):
            values, jacobian = system.evaluate_mp(tuple(point))
            delta = mp.lu_solve(mp.matrix(jacobian), -mp.matrix(values))
            point += delta
            if max(abs(value) for value in delta) < threshold:
                break
        else:
            raise RuntimeError("high-precision Newton seed did not converge")
        values, _ = system.evaluate_mp(tuple(point))
        if max(abs(value) for value in values) > mp.power(10, -(digits - 20)):
            raise RuntimeError("Newton seed residual is unexpectedly large")
        return tuple(+value for value in point)


def mp_to_fraction(value: mp.mpf, digits: int = 225) -> Fraction:
    return Fraction(mp.nstr(value, digits, strip_zeros=False))


@dataclass(frozen=True)
class KrawczykCertificate:
    box: tuple[RI, RI, RI, RI]
    centre: tuple[Fraction, Fraction, Fraction, Fraction]
    image: tuple[RI, RI, RI, RI]
    strict_inclusion: bool
    contraction_inf_norm_upper: Fraction
    image_radius_ratios: tuple[Fraction, Fraction, Fraction, Fraction]
    source_hashes: dict[str, str]


def build_box(seed: Sequence[mp.mpf], xyz_radius_power: int = 180) -> tuple[RI, RI, RI, RI]:
    centres = [mp_to_fraction(value) for value in seed]
    radius = Fraction(1, 10**xyz_radius_power)
    xyz = tuple(RI(value - radius, value + radius) for value in centres[:3])
    return xyz + (RI(decimal_fraction(P5_LO_TEXT), decimal_fraction(P5_HI_TEXT)),)


def certify_krawczyk(system: CandidateSystem, box: Sequence[RI]) -> KrawczykCertificate:
    """Compute and exactly verify K(X) subset int(X)."""

    centre = tuple(interval.midpoint for interval in box)
    f_mid, jac_mid = system.evaluate_fraction(centre)
    inverse = invert_fraction_matrix(jac_mid)
    correction = matvec_fraction(inverse, f_mid)
    newton_centre = [m - d for m, d in zip(centre, correction)]

    _, jac_box = system.evaluate_interval(box)
    c_jac = matmul_fraction_interval(inverse, jac_box)
    remainder_matrix = [
        [RI.point(int(i == j)) - c_jac[i][j] for j in range(4)] for i in range(4)
    ]
    contraction_bound = max(
        sum((entry.abs_upper for entry in row), Fraction(0)) for row in remainder_matrix
    )
    displacement = [interval - m for interval, m in zip(box, centre)]
    remainder = matvec_interval(remainder_matrix, displacement)
    image = tuple(RI.point(n) + r for n, r in zip(newton_centre, remainder))
    strict = all(k.lo > x.lo and k.hi < x.hi for k, x in zip(image, box))
    ratios = tuple(k.width / x.width for k, x in zip(image, box))
    hashes = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in POLY_PATHS + (P5_PATH,)
    }
    return KrawczykCertificate(
        tuple(box), centre, image, strict, contraction_bound, ratios, hashes
    )  # type: ignore[arg-type]


def eval_sympy_rational_interval(expr: sp.Expr, box: Sequence[RI]) -> RI:
    numerator, denominator = sp.cancel(expr).as_numer_denom()
    num = SparsePolynomial.from_sympy(sp.Poly(numerator, *VARIABLES, domain=sp.QQ)).evaluate_interval(box)
    den = SparsePolynomial.from_sympy(sp.Poly(denominator, *VARIABLES, domain=sp.QQ)).evaluate_interval(box)
    return num / den


def reconstruction_denominators(box: Sequence[RI]) -> dict[str, RI]:
    """Intervals for every independent denominator in the rational reconstruction."""

    denominator_t = 2 * X**2 * Z + X * Z**2 + X * Z - 2 * X - 2
    numerator_t = (
        2 * X**2 * Y * Z + 2 * X**2 * Z**2 + 2 * X**2 * Z
        + 3 * X * Y * Z**2 + 3 * X * Y * Z - 2 * X * Y
        + X * Z**3 + 4 * X * Z**2 + X * Z - 2 * X
        + Y * Z**3 + 2 * Y * Z**2 + Y * Z - 2 * Y
        + Z**3 + 2 * Z**2 - Z - 2
    )
    t = numerator_t / denominator_t
    factors = {
        "y": Y,
        "x+1": X + 1,
        "1+z (second pivot)": 1 + Z,
        "D_T": denominator_t,
        "y-T": Y - t,
        "y*(y-T)": Y * (Y - t),
    }
    intervals = {name: eval_sympy_rational_interval(expr, box) for name, expr in factors.items()}
    intervals["T=a42 (reconstructed)"] = eval_sympy_rational_interval(t, box)

    # The third pivot is the (1,1) entry of the second Schur complement.
    a13 = -Z / Y
    a14 = -Z
    a15 = Z * (X + Z) / (X + 1)
    a22 = X + Z + 1
    a23 = -(
        -t * X * Z + X * Y * Z**2 + 2 * X * Y * Z + Y * Z**3
        + 2 * Y * Z**2 - Y
    ) / (Y * (-t + Y))
    a32 = Z
    a33 = -(
        -t * X * Y * Z - t * Y * Z**2 + 2 * t * Y + t * Z
        + X * Y**2 * Z + X * Y * Z**2 + X * Y * Z
        + Y**2 * Z**2 - 2 * Y**2 + Y * Z**3 + 2 * Y * Z**2
        - Y * Z - Y
    ) / (Y * (-t + Y))
    matrix = sp.Matrix(
        [
            [1, 1, a13, a14, a15],
            [X, a22, a23, -1, 1],
            [-1, a32, a33, -1, -1],
            [Y, t, 1, 1, 1],
            [Z, -1, 1, -1, 1],
        ]
    )
    pivot3 = sp.cancel(matrix[:3, :3].det() / matrix[:2, :2].det())
    intervals["p3 (third Schur pivot)"] = eval_sympy_rational_interval(pivot3, box)
    return intervals


def p5_coefficients() -> list[int]:
    with P5_PATH.open() as handle:
        return [int(row["coefficient"]) for row in csv.DictReader(handle)]


def evaluate_ascending(coefficients: Sequence[int], value: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def verify_p5_interval(run_sturm: bool = False) -> dict[str, object]:
    coefficients = p5_coefficients()
    lo, hi = decimal_fraction(P5_LO_TEXT), decimal_fraction(P5_HI_TEXT)
    value_lo = evaluate_ascending(coefficients, lo)
    value_hi = evaluate_ascending(coefficients, hi)
    result: dict[str, object] = {
        "degree": len(coefficients) - 1,
        "lo_sign": -1 if value_lo < 0 else (1 if value_lo > 0 else 0),
        "hi_sign": -1 if value_hi < 0 else (1 if value_hi > 0 else 0),
        "width": str(hi - lo),
    }
    if run_sturm:
        polynomial = sp.Poly(sum(coefficient * G**i for i, coefficient in enumerate(coefficients)), G, domain=sp.ZZ)
        result["sturm_root_count"] = int(
            polynomial.count_roots(sp.Rational(lo.numerator, lo.denominator), sp.Rational(hi.numerator, hi.denominator))
        )
    return result


def certificate_summary(run_sturm: bool = False) -> dict[str, object]:
    system = CandidateSystem.load()
    seed = newton_seed(system)
    box = build_box(seed)
    certificate = certify_krawczyk(system, box)
    denominators = reconstruction_denominators(box)
    return {
        "strict_krawczyk_inclusion": certificate.strict_inclusion,
        "contraction_inf_norm_upper": fraction_decimal(
            certificate.contraction_inf_norm_upper, 15
        ),
        "box": {
            name: {"lo": str(interval.lo), "hi": str(interval.hi)}
            for name, interval in zip(VARIABLE_NAMES, certificate.box)
        },
        "box_decimal": {
            name: {"lo": fraction_decimal(interval.lo, 45), "hi": fraction_decimal(interval.hi, 45)}
            for name, interval in zip(VARIABLE_NAMES, certificate.box)
        },
        "box_exact_decimal": {
            name: {"lo": terminating_decimal(interval.lo), "hi": terminating_decimal(interval.hi)}
            for name, interval in zip(VARIABLE_NAMES, certificate.box)
        },
        "krawczyk_image_decimal": {
            name: {"lo": fraction_decimal(interval.lo, 45), "hi": fraction_decimal(interval.hi, 45)}
            for name, interval in zip(VARIABLE_NAMES, certificate.image)
        },
        "image_width_over_box_width": {
            name: fraction_decimal(ratio, 12)
            for name, ratio in zip(VARIABLE_NAMES, certificate.image_radius_ratios)
        },
        "denominators": {
            name: {
                "lo": fraction_decimal(interval.lo, 30),
                "hi": fraction_decimal(interval.hi, 30),
                "zero_excluded": not interval.contains_zero,
            }
            for name, interval in denominators.items()
        },
        "p5": verify_p5_interval(run_sturm=run_sturm),
        "source_sha256": certificate.source_hashes,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sturm", action="store_true", help="repeat the exact Sturm root count")
    args = parser.parse_args()
    summary = certificate_summary(run_sturm=args.sturm)
    print(json.dumps(summary, indent=2, sort_keys=True))
    if not summary["strict_krawczyk_inclusion"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
