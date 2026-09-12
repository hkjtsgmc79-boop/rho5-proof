/-
D33 / B24Trace — public aggregator
==================================

`import Rho5.Certificate.B24Trace` gives the whole lane:

* `Steps`    — the last three real elimination steps of the D28 reconstruction
  (`pivotSchur (D z) 0 0 = [[r, s], [t, -r]]`, `pivotSchur [[r, s], [t, -r]] 0 0` =
  the `1 × 1` tail `[-(r + st/r)]`, `pivotSchur` of that tail = the `0 × 0` matrix),
  the pivot values, the `Physical.height` connection `-(r + st/r) = -z 23`, and
  `F = z 23 > 0` from `r > 0`, `0 ≤ s`, `0 ≤ t`;
* `Legality` — completeness and non-vanishing of the last three pivots under exactly
  the card's conditions (`Physical z`, `HeadBand z`, `0 < p z`, `0 < z 0`,
  `0 ≤ z 2`, `z 2 ≤ z 1`, `0 ≤ z 3`);
* `Trace`    — **item 3**: `LegalTrace (reconstruct z) [1, p z, z 0, z 1, z 23]`,
  with every step a real `LegalTrace.step`, the values literal absolute values, and
  the `0 × 0` end the empty trace (no extra `0`);
* `Growth`   — **item 4**: `growthRatio (reconstruct z) [1, p z, z 0, z 1, z 23]`
  equals the D17 `tracePeak` of that list, `z 23 ≤ growthRatio`, and the conditional
  `growthRatio = z 23` given the four explicit bounds `1, p, k, r ≤ z 23`.

Reused unchanged (read-only): D28's `Rho5.Certificate.B24Reconstruction`
(`reconstruct`, `firstStage`, `p`, `HeadBand`, `matrixEntryMax_reconstruct`,
`isCompletePivot_reconstruct_zero_zero`, `isCompletePivot_firstStage_zero_zero`,
`pivotSchur_reconstruct_zero_zero`, `pivotSchur_firstStage_zero_zero`), the frozen
pilot `Rho5.Certificate.B16Model` (`Point`, `D`, `Physical`), D10's
`Rho5.PivotReindex.pivotSchur`, D13's `Rho5.CompletePivotPath.LegalTrace`, and D17's
`Rho5.GrowthModel.{tracePeak, growthRatio, le_tracePeak, tracePeak_le}`.

Scope (the remaining chain, **not** proved here):

1. **existence**: that any point satisfies the full condition list (no witness is
   produced, and the trace hypothesis is not discharged for an arbitrary matrix);
2. **inverse normalization**: an arbitrary real `Matrix5` into the same-source
   parameterization (macro-class coverage) — still absent;
3. the *sourced* attainment statement (a matrix whose parameters provably satisfy the
   bounds, hence `growthRatio = z 23`), and anything about `alpha` or `sSup`;
4. the G04 critical-existence path, which is owned elsewhere and is not touched.

This lane connects the already-paid forward reconstruction to the real `LegalTrace`
and the real growth ratio; it claims no completion of the RHO5 programme.
-/
import Rho5.Certificate.B24Trace.Steps
import Rho5.Certificate.B24Trace.Legality
import Rho5.Certificate.B24Trace.Trace
import Rho5.Certificate.B24Trace.Growth
