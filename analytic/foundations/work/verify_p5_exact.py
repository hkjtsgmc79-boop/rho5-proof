#!/usr/bin/env python3
"""Exact rational checks for the recomputed degree-61 factor."""

import csv
import json
import math
import time
from fractions import Fraction
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
rows = list(csv.DictReader((ROOT / "P5_coefficients_ascending.csv").open()))
coefficients = [int(row["coefficient"]) for row in rows]

L_TEXT = (
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560269"
)
U_TEXT = (
    "4.13251707863247285422334685327737126995279153779908769454418052196743783429681764825855179985483022630152515659887825271609554209934703653072223897312925069088264378769458915450759171541549166637560270"
)


def decimal_fraction(text: str) -> Fraction:
    whole, fractional = text.split(".")
    return Fraction(int(whole + fractional), 10 ** len(fractional))


def evaluate_ascending(coeffs: list[int], value: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(coeffs):
        result = result * value + coefficient
    return result


started = time.time()
L, U = decimal_fraction(L_TEXT), decimal_fraction(U_TEXT)
value_L = evaluate_ascending(coefficients, L)
value_U = evaluate_ascending(coefficients, U)

g = sp.symbols("g")
poly = sp.Poly(sum(c * g**i for i, c in enumerate(coefficients)), g, domain=sp.ZZ)
root_count = int(poly.count_roots(sp.Rational(L.numerator, L.denominator), sp.Rational(U.numerator, U.denominator)))

summary = {
    "degree": poly.degree(),
    "content": math.gcd(*map(abs, coefficients)),
    "P5_L_sign": -1 if value_L < 0 else (1 if value_L > 0 else 0),
    "P5_U_sign": -1 if value_U < 0 else (1 if value_U > 0 else 0),
    "roots_in_interval": root_count,
    "interval_decimal_width": f"1e-{len(L_TEXT.split('.')[1])}",
    "elapsed_seconds": time.time() - started,
}
(ROOT / "P5_exact_verification.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
