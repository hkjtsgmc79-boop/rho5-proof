#!/usr/bin/env python3
"""Build Singular input for the z-discriminant and its factorization."""

from pathlib import Path


ROOT = Path(__file__).resolve().parent
P = (ROOT / "P_zg_singular.txt").read_text().strip()
TARGET = ROOT / "factor_discriminant.sing"

program = f"""option(prot);
ring r = 0,(z,g),lp;
poly P = {P};
poly dP = diff(P,z);
poly R = resultant(P,dP,z);
ideal F = factorize(R,1);
write("work/singular_discriminant_summary.txt", deg(R));
write("work/singular_discriminant_summary.txt", size(F));
for (int i=1; i<=size(F); i++)
{{
  write("work/singular_discriminant_factors.txt", "BEGIN_FACTOR");
  write("work/singular_discriminant_factors.txt", i);
  write("work/singular_discriminant_factors.txt", F[i]);
  write("work/singular_discriminant_factors.txt", "END_FACTOR");
}}
exit;
"""
TARGET.write_text(program)
print(TARGET)
