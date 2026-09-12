/-
D28 / B24Reconstruction — public aggregator
==========================================

`import Rho5.Certificate.B24Reconstruction` gives the whole lane:

* `Basic`       — the B24 coordinate reading (`p`, `e`, `beta`, `F`, `x`), the
  coordinate correspondence lemmas against the frozen `B16Model`
  (`u_coord`, `x_coord`, `v_coord`, `q_coord`, `D_coord`, `L_doc`, `P_doc`, `S_doc`,
  `O_doc`), the `Physical` field readings, the explicit head band `HeadBand`, and the
  reconstruction `reconstruct` / `firstStage` with their entry tables
  (`reconstruct_table`, `firstStage_table`);
* `FirstPivot`  — `pivotSchur (reconstruct z) 0 0 = firstStage z` (card item 1);
* `SecondPivot` — `p ≠ 0 → pivotSchur (firstStage z) 0 0 = B16.D z` (card item 2);
* `PivotLegal`  — `matrixEntryMax (reconstruct z) = 1`, `IsCompletePivot` and
  `PivotReady` at `(0, 0)` for the reconstructed matrix and for the first stage
  (card item 3).

Reused unchanged (read-only): `Rho5.Certificate.B16.{Point, D, O, S, L, P, u, xv, v,
q, Physical}` (frozen first round), `Rho5.Matrix5`, `Rho5.matrixEntryMax`,
`Rho5.Pivot.{IsCompletePivot, fixedSchur}` (frozen conventions/pivot), and
`Rho5.PivotReindex.{pivotSchur, movePivot_zero_zero_eq, PivotReady,
pivotReady_of_ne_zero}` (D10), together with
`Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax` (D08).

Scope (the remaining chain, **not** proved here):

1. the last two tail pivots `k`, `r` of the five-step path, and the fourth/fifth
   pivot entries (`r` and `-F`) with the height law `F = r + st/r`;
2. the five-step `LegalTrace` (the frozen `Rho5.Shared.CompletePivotPath` layer) and
   the growth ratio / global normalization interface (D17's `GrowthModel`);
3. the inverse direction: an arbitrary real `Matrix5` normalized into this
   same-source parameterization (macro-class coverage), which is what would make the
   reconstruction a *complete* model of the B×22 problem.

This lane proves the forward reconstruction and the first two real elimination steps
only; it makes no claim about all matrices, about numerical search, or about the G04
critical-existence path.
-/
import Rho5.Certificate.B24Reconstruction.Basic
import Rho5.Certificate.B24Reconstruction.FirstPivot
import Rho5.Certificate.B24Reconstruction.SecondPivot
import Rho5.Certificate.B24Reconstruction.PivotLegal
