#!/usr/bin/env python3
"""Exact rational primal/complete-pivot certificate for the 5x5 candidate.

This module closes the primal half of the candidate Chebyshev certificate.
It uses the already certified 1e-180 root box from
``candidate_interval_newton.py`` and the paper's rational reconstruction.

All inequality decisions use closed intervals whose endpoints are
``fractions.Fraction`` objects.  Boundary equalities are never decided by a
tolerance: they are recognized either as rational-function identities or as
exact consequences of the certified root equations P1=P2=P3=0.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence

import sympy as sp

from candidate_interval_newton import (
    CandidateSystem,
    G as GROWTH,
    X,
    Y,
    Z,
    VARIABLES,
    SparsePolynomial,
    certify_krawczyk,
)
from rational_interval import RationalInterval as RI


ROOT = Path(__file__).resolve().parents[1]

# These are exactly the finite-decimal centres printed in R5.  The x,y,z
# radius is exactly 10^-180; the g interval is the exact Sturm box from R5.
ROOT_CENTRES = (
    Fraction(
        "-0.617532676881827094746042947571661401679120923943678170913721662445069183926915599430351537888841625933642529130574661908950219815216174796092552441790484640472601736577335944496440991252250721448896969081867577435416766560108"
    ),
    Fraction(
        "-0.779150742216311061144934942459038900301281850854312081668422760365271742335015447212481930082268450983863651857926663281063368672667450988457321392459417010071603914261937195685134244418622142845316315647135946460051943986519"
    ),
    Fraction(
        "0.453224909846837467183709959977529473640881626821152195148225061062990962144765019673420236660910849584214877622458824690105378454219470392948909375556264458495010224674420035639015853124582109276572435805320420126271854303861"
    ),
)
G_LO = Fraction(
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560269"
)
G_HI = Fraction(
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560270"
)


def certified_root_box() -> tuple[RI, RI, RI, RI]:
    radius = Fraction(1, 10**180)
    return tuple(RI(c - radius, c + radius) for c in ROOT_CENTRES) + (RI(G_LO, G_HI),)  # type: ignore[return-value]


def cancel_matrix(matrix: sp.Matrix) -> sp.Matrix:
    return matrix.applyfunc(sp.cancel)


def one_step_schur(matrix: sp.Matrix) -> sp.Matrix:
    """Eliminate the leading scalar, cancelling every resulting entry."""

    pivot = matrix[0, 0]
    return sp.Matrix(
        matrix.rows - 1,
        matrix.cols - 1,
        lambda i, j: sp.cancel(
            matrix[i + 1, j + 1]
            - matrix[i + 1, 0] * matrix[0, j + 1] / pivot
        ),
    )


@dataclass(frozen=True)
class Reconstruction:
    A: sp.Matrix
    F: sp.Matrix
    G: sp.Matrix
    H: sp.Matrix
    L: sp.Matrix
    p2: sp.Expr
    p3: sp.Expr
    h: sp.Expr
    t: sp.Expr


def reconstruct_symbolically() -> Reconstruction:
    """Rebuild the paper candidate from (x,y,z,g), without decimals."""

    denominator_t = 2 * X**2 * Z + X * Z**2 + X * Z - 2 * X - 2
    numerator_t = (
        2 * X**2 * Y * Z
        + 2 * X**2 * Z**2
        + 2 * X**2 * Z
        + 3 * X * Y * Z**2
        + 3 * X * Y * Z
        - 2 * X * Y
        + X * Z**3
        + 4 * X * Z**2
        + X * Z
        - 2 * X
        + Y * Z**3
        + 2 * Y * Z**2
        + Y * Z
        - 2 * Y
        + Z**3
        + 2 * Z**2
        - Z
        - 2
    )
    t = sp.cancel(numerator_t / denominator_t)
    a13 = -Z / Y
    a14 = -Z
    a15 = Z * (X + Z) / (X + 1)
    a22 = X + Z + 1
    a23 = -(
        -t * X * Z
        + X * Y * Z**2
        + 2 * X * Y * Z
        + Y * Z**3
        + 2 * Y * Z**2
        - Y
    ) / (Y * (-t + Y))
    a32 = Z
    a33 = -(
        -t * X * Y * Z
        - t * Y * Z**2
        + 2 * t * Y
        + t * Z
        + X * Y**2 * Z
        + X * Y * Z**2
        + X * Y * Z
        + Y**2 * Z**2
        - 2 * Y**2
        + Y * Z**3
        + 2 * Y * Z**2
        - Y * Z
        - Y
    ) / (Y * (-t + Y))
    A = cancel_matrix(
        sp.Matrix(
            (
                (1, 1, a13, a14, a15),
                (X, a22, a23, -1, 1),
                (-1, a32, a33, -1, -1),
                (Y, t, 1, 1, 1),
                (Z, -1, 1, -1, 1),
            )
        )
    )
    F = one_step_schur(A)
    G = one_step_schur(F)
    H = one_step_schur(G)
    L = one_step_schur(H)
    return Reconstruction(A=A, F=F, G=G, H=H, L=L, p2=F[0, 0], p3=G[0, 0], h=H[0, 0], t=t)


def evaluate(expr: sp.Expr, box: Sequence[RI]) -> RI:
    """Evaluate a rational function with exact rational interval endpoints."""

    numerator, denominator = sp.cancel(expr).as_numer_denom()
    num_poly = SparsePolynomial.from_sympy(
        sp.Poly(numerator, *VARIABLES, domain=sp.QQ)
    )
    den_poly = SparsePolynomial.from_sympy(
        sp.Poly(denominator, *VARIABLES, domain=sp.QQ)
    )
    denominator_interval = den_poly.evaluate_interval(box)
    if denominator_interval.contains_zero:
        raise ZeroDivisionError(f"denominator interval contains zero: {denominator}")
    return num_poly.evaluate_interval(box) / denominator_interval


def polynomial_from_file(name: str) -> sp.Poly:
    expr = sp.sympify(
        (ROOT / "work" / "sympy_recompute" / name).read_text(),
        locals={"x": X, "y": Y, "z": Z, "g": GROWTH},
    )
    return sp.Poly(expr, *VARIABLES, domain=sp.QQ)


def root_polynomial_implies_relation(
    expr: sp.Expr, polynomial: sp.Poly, box: Sequence[RI]
) -> bool:
    """Verify ``polynomial=0 => expr=0`` on ``box`` exactly.

    The saved P1/P2/P3 were deliberately produced from an uncancelled
    numerator, so each can contain nonzero reconstruction factors.  We divide
    exactly in QQ[x,y,z,g] and prove the quotient factor does not vanish on
    the root box.  Merely comparing expanded numerators would incorrectly
    reject these legitimate factors; merely ignoring them would be unsound.
    """

    numerator, denominator = sp.cancel(expr).as_numer_denom()
    candidate = sp.Poly(numerator, *VARIABLES, domain=sp.QQ)
    if candidate.is_zero:
        return True
    quotient, remainder = polynomial.div(candidate)
    if not remainder.is_zero or quotient.is_zero:
        return False
    quotient_interval = evaluate(quotient.as_expr(), box)
    denominator_interval = evaluate(denominator, box)
    return (
        not quotient_interval.contains_zero
        and not denominator_interval.contains_zero
    )


@dataclass(frozen=True)
class EntryCheck:
    stage: str
    row: int
    column: int
    relation: str
    enclosure: RI
    slack_lower: Fraction

    @property
    def is_strict(self) -> bool:
        return self.relation == "strict"


def classify_entry(
    stage: str,
    row: int,
    column: int,
    entry: sp.Expr,
    pivot: sp.Expr,
    box: Sequence[RI],
) -> EntryCheck:
    """Prove entry = +/-pivot identically, or prove strict domination."""

    entry = sp.cancel(entry)
    pivot = sp.cancel(pivot)
    enclosure = evaluate(entry, box)
    if sp.cancel(entry - pivot) == 0:
        return EntryCheck(stage, row, column, "+pivot identity", enclosure, Fraction(0))
    if sp.cancel(entry + pivot) == 0:
        return EntryCheck(stage, row, column, "-pivot identity", enclosure, Fraction(0))
    plus_slack = evaluate(pivot + entry, box)
    minus_slack = evaluate(pivot - entry, box)
    slack = min(plus_slack.lo, minus_slack.lo)
    if slack <= 0:
        raise AssertionError(
            f"failed strict |entry|<pivot check at {stage}[{row},{column}]"
        )
    return EntryCheck(stage, row, column, "strict", enclosure, slack)


def check_matrix(
    stage: str, matrix: sp.Matrix, pivot: sp.Expr, box: Sequence[RI]
) -> tuple[EntryCheck, ...]:
    return tuple(
        classify_entry(stage, i + 1, j + 1, matrix[i, j], pivot, box)
        for i in range(matrix.rows)
        for j in range(matrix.cols)
    )


@dataclass(frozen=True)
class ResidualCheck:
    column: int
    component: int
    source: str
    check: EntryCheck


@dataclass(frozen=True)
class PrimalData:
    B: sp.Matrix
    d_columns: tuple[sp.Matrix, sp.Matrix, sp.Matrix]
    r_columns: tuple[sp.Matrix, sp.Matrix, sp.Matrix]
    residuals: tuple[sp.Matrix, sp.Matrix, sp.Matrix]
    checks: tuple[ResidualCheck, ...]


def build_primal_data(
    reconstruction: Reconstruction, box: Sequence[RI]
) -> PrimalData:
    """Construct the exact lift residuals and certify their unit bound."""

    A, F, G, p2, p3 = (
        reconstruction.A,
        reconstruction.F,
        reconstruction.G,
        reconstruction.p2,
        reconstruction.p3,
    )
    b = A[1, 0]
    u = sp.Matrix(A[2:, 0])
    v = sp.Matrix(1, 3, lambda _, j: A[0, j + 2]).T
    x = sp.Matrix(3, 1, lambda i, _: sp.cancel(F[i + 1, 0] / p2))
    y = sp.Matrix(3, 1, lambda j, _: sp.cancel(F[0, j + 1] / p2))
    C = cancel_matrix(G / p3)
    B = sp.Matrix(
        (
            (1, 0),
            (0, 1),
            (b, p2),
            (0, x[0]),
            (0, x[1]),
            (0, x[2]),
            (u[0], p2 * x[0]),
            (u[1], p2 * x[1]),
            (u[2], p2 * x[2]),
        )
    ).applyfunc(sp.cancel)

    d_columns: list[sp.Matrix] = []
    r_columns: list[sp.Matrix] = []
    residuals: list[sp.Matrix] = []
    checks: list[ResidualCheck] = []
    for j in range(3):
        d = sp.Matrix(
            (
                0,
                0,
                0,
                C[0, j] / p2,
                C[1, j] / p2,
                C[2, j] / p2,
                C[0, j],
                C[1, j],
                C[2, j],
            )
        ).applyfunc(sp.cancel)
        r = sp.Matrix((v[j], y[j]))
        residual = (B * r + p3 * d).applyfunc(sp.cancel)
        expected = sp.Matrix(
            (
                A[0, j + 2],
                F[0, j + 1] / p2,
                A[1, j + 2],
                F[1, j + 1] / p2,
                F[2, j + 1] / p2,
                F[3, j + 1] / p2,
                A[2, j + 2],
                A[3, j + 2],
                A[4, j + 2],
            )
        ).applyfunc(sp.cancel)
        if any(sp.cancel(a - b_) != 0 for a, b_ in zip(residual, expected)):
            raise AssertionError(f"lift residual identity failed in column {j + 1}")
        # This is the actual primal point for delta_j.
        primal_value = (B * (r / p3) + d).applyfunc(sp.cancel)
        if any(
            sp.cancel(a - b_ / p3) != 0
            for a, b_ in zip(primal_value, residual)
        ):
            raise AssertionError(f"scaled primal identity failed in column {j + 1}")

        source_names = (
            f"A[1,{j + 3}]",
            f"F[1,{j + 2}]/p2",
            f"A[2,{j + 3}]",
            f"F[2,{j + 2}]/p2",
            f"F[3,{j + 2}]/p2",
            f"F[4,{j + 2}]/p2",
            f"A[3,{j + 3}]",
            f"A[4,{j + 3}]",
            f"A[5,{j + 3}]",
        )
        for i, (entry, source) in enumerate(zip(residual, source_names), 1):
            check = classify_entry(
                "residual", i, j + 1, entry, sp.Integer(1), box
            )
            checks.append(ResidualCheck(j + 1, i, source, check))
        d_columns.append(d)
        r_columns.append(r)
        residuals.append(residual)
    return PrimalData(
        B,
        tuple(d_columns),  # type: ignore[arg-type]
        tuple(r_columns),  # type: ignore[arg-type]
        tuple(residuals),  # type: ignore[arg-type]
        tuple(checks),
    )


@dataclass(frozen=True)
class Certificate:
    root_box: tuple[RI, RI, RI, RI]
    reconstruction: Reconstruction
    krawczyk_strict: bool
    root_equation_matches: tuple[bool, bool, bool]
    core_tail_identity: bool
    pivot_intervals: tuple[RI, RI, RI, RI, RI]
    A_checks: tuple[EntryCheck, ...]
    F_checks: tuple[EntryCheck, ...]
    G_checks: tuple[EntryCheck, ...]
    C_checks: tuple[EntryCheck, ...]
    primal: PrimalData


def build_certificate(recheck_krawczyk: bool = True) -> Certificate:
    box = certified_root_box()
    rec = reconstruct_symbolically()

    system = CandidateSystem.load()
    if recheck_krawczyk:
        krawczyk_strict = certify_krawczyk(system, box).strict_inclusion
        if not krawczyk_strict:
            raise AssertionError("the literal R5 root box failed Krawczyk recertification")
    else:
        krawczyk_strict = True

    root_polynomials = tuple(polynomial_from_file(f"p{i}.txt") for i in (1, 2, 3))
    root_relations = (
        rec.H[0, 0] + rec.H[1, 0],
        rec.H[0, 0] - rec.H[1, 1],
        GROWTH - 2 * rec.H[0, 0],
    )
    matches = tuple(
        root_polynomial_implies_relation(relation, polynomial, box)
        for relation, polynomial in zip(root_relations, root_polynomials)
    )
    if matches != (True, True, True):
        raise AssertionError("H-tail relations do not match P1,P2,P3")
    if sp.cancel(rec.H[0, 0] - rec.H[0, 1]) != 0:
        raise AssertionError("the reconstructed H11=H12 identity failed")

    p1 = sp.Integer(1)
    p2 = rec.p2
    p3 = rec.p3
    # At the certified root, P3=0 gives h=g/2 exactly.  We evaluate g/2,
    # not a naturally expanded H expression, when certifying its sign.
    h_root = GROWTH / 2
    p5_root = GROWTH
    pivots = tuple(evaluate(expr, box) for expr in (p1, p2, p3, h_root, p5_root))
    if any(interval.lo <= 0 for interval in pivots):
        raise AssertionError("a candidate pivot was not certified positive")

    A_checks = check_matrix("A", rec.A, p1, box)
    F_checks = check_matrix("F", rec.F, p2, box)
    G_checks = check_matrix("G", rec.G, p3, box)
    C = cancel_matrix(rec.G / p3)
    C_checks = check_matrix("C", C, sp.Integer(1), box)
    core_tail = one_step_schur(C)
    core_tail_identity = all(
        sp.cancel(core_tail[i, j] - rec.H[i, j] / p3) == 0
        for i in range(2)
        for j in range(2)
    )
    if not core_tail_identity:
        raise AssertionError("Schur(C)=H/p3 identity failed")

    # The first three stages must have precisely the prescribed exact
    # boundary counts: 14 fixed A entries, 5 F entries, and 4 G/C entries.
    identity_counts = tuple(
        sum(not check.is_strict for check in checks)
        for checks in (A_checks, F_checks, G_checks, C_checks)
    )
    if identity_counts != (14, 5, 4, 4):
        raise AssertionError(f"unexpected boundary counts: {identity_counts}")

    primal = build_primal_data(rec, box)
    return Certificate(
        root_box=box,
        reconstruction=rec,
        krawczyk_strict=krawczyk_strict,
        root_equation_matches=matches,  # type: ignore[arg-type]
        core_tail_identity=core_tail_identity,
        pivot_intervals=pivots,  # type: ignore[arg-type]
        A_checks=A_checks,
        F_checks=F_checks,
        G_checks=G_checks,
        C_checks=C_checks,
        primal=primal,
    )


def _fraction_scientific(value: Fraction, digits: int = 12) -> str:
    """Human-readable diagnostic only; all decisions precede this call."""

    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    value = abs(value)
    exponent = len(str(value.numerator)) - len(str(value.denominator))
    scaled = value / (Fraction(10) ** exponent)
    while scaled >= 10:
        scaled /= 10
        exponent += 1
    while scaled < 1:
        scaled *= 10
        exponent -= 1
    scale = 10 ** (digits - 1)
    mantissa = Fraction((scaled * scale).numerator // (scaled * scale).denominator, scale)
    return f"{sign}{float(mantissa):.{digits - 1}f}e{exponent:+d}"


def summary(certificate: Certificate) -> dict[str, object]:
    def checks_summary(checks: Sequence[EntryCheck]) -> list[dict[str, object]]:
        return [
            {
                "entry": f"{check.stage}[{check.row},{check.column}]",
                "relation": check.relation,
                "lo": _fraction_scientific(check.enclosure.lo),
                "hi": _fraction_scientific(check.enclosure.hi),
                "slack_lower": _fraction_scientific(check.slack_lower),
            }
            for check in checks
        ]

    residual_checks = [item.check for item in certificate.primal.checks]
    return {
        "krawczyk_strict": certificate.krawczyk_strict,
        "root_equation_matches": certificate.root_equation_matches,
        "core_tail_identity": certificate.core_tail_identity,
        "root_exact_tail_pattern": "H=(g/2)*[[1,1],[-1,1]], q(C)=g/p3",
        "pivot_intervals": [
            {"lo": _fraction_scientific(x.lo), "hi": _fraction_scientific(x.hi)}
            for x in certificate.pivot_intervals
        ],
        "identity_counts": {
            "A": sum(not c.is_strict for c in certificate.A_checks),
            "F": sum(not c.is_strict for c in certificate.F_checks),
            "G": sum(not c.is_strict for c in certificate.G_checks),
            "C": sum(not c.is_strict for c in certificate.C_checks),
            "residual": sum(not c.is_strict for c in residual_checks),
        },
        "minimum_strict_slack": {
            "A": _fraction_scientific(min(c.slack_lower for c in certificate.A_checks if c.is_strict)),
            "F": _fraction_scientific(min(c.slack_lower for c in certificate.F_checks if c.is_strict)),
            "G": _fraction_scientific(min(c.slack_lower for c in certificate.G_checks if c.is_strict)),
            "C": _fraction_scientific(min(c.slack_lower for c in certificate.C_checks if c.is_strict)),
            "residual": _fraction_scientific(min(c.slack_lower for c in residual_checks if c.is_strict)),
        },
        "A": checks_summary(certificate.A_checks),
        "F": checks_summary(certificate.F_checks),
        "G": checks_summary(certificate.G_checks),
        "C": checks_summary(certificate.C_checks),
        "residuals": [
            {
                "column": item.column,
                "component": item.component,
                "source": item.source,
                **checks_summary((item.check,))[0],
            }
            for item in certificate.primal.checks
        ],
        "primal_conclusion": "delta_j <= 1/p3 for j=1,2,3",
    }


def main() -> None:
    certificate = build_certificate(recheck_krawczyk=True)
    print(json.dumps(summary(certificate), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
