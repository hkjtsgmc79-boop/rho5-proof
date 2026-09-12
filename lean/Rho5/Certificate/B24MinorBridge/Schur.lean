import Rho5.Certificate.B24Trace
import Rho5.Certificate.B24Extraction
import Rho5.Shared.CanonicalTail

/-!
# D71 / B24MinorBridge — the paid Schur identities along `reconstruct z`

The bridge from a qualified B24 point `z` to the minor domain starts by identifying the
D37 readings of the actual matrix `M = reconstruct z` with the paid steps of D28
(`firstStage`) and D33 (`tail2`, `tail1`):

* `S4 M = firstStage z` — D28's first step, no hypothesis;
* `S3 M = D z` — D28's second step, using `p z ≠ 0`;
* `T2 M = tail2 z` — D33's third step, using `z 0 ≠ 0`;
* hence the scalar readings `p M = z 8`, `k M = z 0`, `r M = z 1`, `s M = z 2`, `t M = z 3`,
  the tail diagonal `T2 M 1 1 = -z 1`, and D48's coordinate `delta M = -z 23`.

Nothing is reproved here: each line is one of D28's / D33's paid theorems, transported
along the definition of the D37 reading.  The three `tail2` entry readings are the
definitional unfolding of D33's own `tail2` (as its `tail2_zero_zero` already is).
-/

namespace Rho5.Certificate.B24MinorBridge

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage HeadBand)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The three later Schur updates are the paid D28/D33 matrices -/

/-- **First step (D28).**  `S4 (reconstruct z) = firstStage z`, with no hypothesis. -/
theorem S4_reconstruct (z : Point) : S4 (reconstruct z) = firstStage z :=
  Rho5.Certificate.B24Reconstruction.pivotSchur_reconstruct_zero_zero z

/-- **Second step (D28).**  `S3 (reconstruct z) = D z`, using `p z ≠ 0`. -/
theorem S3_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0) :
    S3 (reconstruct z) = Rho5.Certificate.B16.D z := by
  rw [Rho5.Certificate.B24Extraction.S3, S4_reconstruct]
  exact Rho5.Certificate.B24Reconstruction.pivotSchur_firstStage_zero_zero z hp

/-- **Third step (D33).**  `T2 (reconstruct z) = tail2 z`, using `p z ≠ 0` and `z 0 ≠ 0`. -/
theorem T2_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0)
    (hk : z 0 ≠ 0) : T2 (reconstruct z) = Rho5.Certificate.B24Trace.tail2 z := by
  rw [Rho5.Certificate.B24Extraction.T2, S3_reconstruct z hp]
  exact Rho5.Certificate.B24Trace.pivotSchur_D_zero_zero z hk

/-! ## 2. Definitional entry readings of D33's `tail2 = !![z 1, z 2; z 3, -z 1]` -/

/-- `tail2 z 0 1 = z 2` (unfolds D33's own definition, as `tail2_zero_zero` does). -/
theorem tail2_zero_one (z : Point) : Rho5.Certificate.B24Trace.tail2 z 0 1 = z 2 := by
  simp [Rho5.Certificate.B24Trace.tail2]

/-- `tail2 z 1 0 = z 3`. -/
theorem tail2_one_zero (z : Point) : Rho5.Certificate.B24Trace.tail2 z 1 0 = z 3 := by
  simp [Rho5.Certificate.B24Trace.tail2]

/-- `tail2 z 1 1 = -z 1` (the balanced tail diagonal). -/
theorem tail2_one_one (z : Point) : Rho5.Certificate.B24Trace.tail2 z 1 1 = -z 1 := by
  simp [Rho5.Certificate.B24Trace.tail2]

/-! ## 3. The actual readings of the reconstructed matrix -/

/-- `p (reconstruct z) = z 8`. -/
theorem p_reconstruct (z : Point) : p (reconstruct z) = z 8 := by
  rw [Rho5.Certificate.B24Extraction.p, S4_reconstruct,
    Rho5.Certificate.B24Reconstruction.firstStage_zero_zero,
    Rho5.Certificate.B24Reconstruction.p_coord]

/-- `k (reconstruct z) = z 0`. -/
theorem k_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0) :
    k (reconstruct z) = z 0 := by
  rw [Rho5.Certificate.B24Extraction.k, S3_reconstruct z hp,
    Rho5.Certificate.B24Trace.D_zero_zero]

/-- `r (reconstruct z) = z 1`. -/
theorem r_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0)
    (hk : z 0 ≠ 0) : r (reconstruct z) = z 1 := by
  rw [Rho5.Certificate.B24Extraction.r, T2_reconstruct z hp hk,
    Rho5.Certificate.B24Trace.tail2_zero_zero]

/-- `s (reconstruct z) = z 2`. -/
theorem s_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0)
    (hk : z 0 ≠ 0) : s (reconstruct z) = z 2 := by
  rw [Rho5.Certificate.B24Extraction.s, T2_reconstruct z hp hk, tail2_zero_one]

/-- `t (reconstruct z) = z 3`. -/
theorem t_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0)
    (hk : z 0 ≠ 0) : t (reconstruct z) = z 3 := by
  rw [Rho5.Certificate.B24Extraction.t, T2_reconstruct z hp hk, tail2_one_zero]

/-- The tail diagonal: `T2 (reconstruct z) 1 1 = -z 1`. -/
theorem T2_one_one_reconstruct (z : Point) (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0)
    (hk : z 0 ≠ 0) : T2 (reconstruct z) 1 1 = -z 1 := by
  rw [T2_reconstruct z hp hk, tail2_one_one]

/-- **D48's tail coordinate on the reconstruction: `delta (reconstruct z) = -z 23`**,
via D48's `delta_eq_pivotSchur`, D33's fourth step and D33's height identity. -/
theorem delta_reconstruct (z : Point) (hz : Physical z)
    (hp : Rho5.Certificate.B24Reconstruction.p z ≠ 0) (hk : z 0 ≠ 0) :
    Rho5.CanonicalTail.delta (reconstruct z) = -z 23 := by
  have hr : z 1 ≠ 0 := ne_of_gt (Rho5.Certificate.B24Reconstruction.r_pos hz)
  rw [Rho5.CanonicalTail.delta_eq_pivotSchur, T2_reconstruct z hp hk,
    Rho5.Certificate.B24Trace.pivotSchur_tail2_zero_zero z hr,
    Rho5.Certificate.B24Trace.tail1_zero_zero_height z hz]

end Rho5.Certificate.B24MinorBridge
