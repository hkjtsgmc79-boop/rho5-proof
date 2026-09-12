/-
D37 / B24Extraction — public aggregator
=======================================

`import Rho5.Certificate.B24Extraction` gives the whole lane: the inverse interface
from a normalized real `5 × 5` matrix with a balanced tail back to the original B24
coordinates.

* `Extract` — the three successive Schur updates `S4`, `S3`, `T2`, the extracted
  scalars `p, k, r, s, t, F`, the point `extract A`, the entrywise Schur formulas,
  the coordinate-evaluation lemmas of the frozen accessors, **item 1** (the
  definition) and **item 2**: `reconstruct (extract A) = A` together with the block
  correspondences `D (extract A) = S3 A`, `S (extract A) = S4`'s lower block,
  `O (extract A) = A`'s lower block, and the `L`, `P`, `q` rows/columns.
* `Bands`   — **item 3**: `HeadBand (extract A)` and `Physical (extract A)`, both
  *proved* from the pivot bounds of `A`, `S4`, `S3`, `T2` (no predicate is assumed).
* `Trace`   — **item 4**: `LegalTrace A [1, p A, k A, r A, F A]`, the growth bound
  `F A ≤ growthRatio A […]`, and the conditional equality under the four extra
  bounds `1, p, k, r ≤ F`.

Standing hypotheses of the class (all explicit, never assumed silently):
`A 0 0 = 1` (normalization), `p A ≠ 0`, `k A ≠ 0`, `T2 A 1 1 = -r A` (balanced tail),
the complete pivots at `(0,0)` of `A`, `S4`, `S3`, `T2`, and the positivity
`0 < p A`, `0 < k A`, `0 < r A`; item 4 additionally uses `0 ≤ s A`, `0 ≤ t A`.

Reused unchanged (read-only): D28's `Rho5.Certificate.B24Reconstruction`
(`reconstruct`, `firstStage`, `HeadBand`, `Physical`'s model, `D`, `O`, `S`, `L`, `P`,
`u`, `xv`, `v`, `q`, `matrixEntryMax_reconstruct`, the two `pivotSchur` step theorems),
D10's `Rho5.PivotReindex.pivotSchur` and `Rho5.Pivot.IsCompletePivot`, D13's
`Rho5.CompletePivotPath.LegalTrace`, D33's `Rho5.Certificate.B24Trace`
(`legalTrace_reconstruct`, `le_growthRatio_z23`, `growthRatio_eq_z23`), and D17's
`Rho5.GrowthModel.{growthRatio, tracePeak}`.

Scope — **not** proved here (the card's unpaid list):

1. the classification/transformation of an **arbitrary** matrix into this normalized
   balanced-tail class (macro-class coverage): the class is a hypothesis, not a
   theorem about all matrices;
2. the **existence** of a matrix in the class (no witness is produced);
3. attainment of `alpha`, any sharp global upper bound, or anything about `sSup`;
4. the G04 critical-existence path, which belongs to another lane.

This is a practical inverse interface, not a new classification theorem.
-/
import Rho5.Certificate.B24Extraction.Extract
import Rho5.Certificate.B24Extraction.Bands
import Rho5.Certificate.B24Extraction.Trace
