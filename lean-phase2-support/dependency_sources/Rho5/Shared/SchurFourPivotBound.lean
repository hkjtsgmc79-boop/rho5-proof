import Rho5.Shared.SchurFourPivotBound.Embed
import Rho5.Shared.SchurFourPivotBound.Bound

/-!
# D138 — `Rho5.Shared.SchurFourPivotBound`

The paper's first-Schur fourth-pivot bound: `TS.height M ≤ 4 * B24Extraction.p M` for every
`TS.LeadingInput M` (`Bound.height_le_four_mul_p`), obtained by embedding the actual `4 x 4` first
Schur complement into a `5 x 5` matrix with a zero last row and column (`Embed.padLast`), lifting
the real all-`(0,0)` complete-pivot path (`Embed.ZeroTrace`), and applying D124's already-proved
`ExternalFourthPivot.early_pivot_bounds_including_zero`.  No hypothesis beyond `LeadingInput` is
used, and `F ≤ 4p` is a conclusion, never an assumption.
-/
