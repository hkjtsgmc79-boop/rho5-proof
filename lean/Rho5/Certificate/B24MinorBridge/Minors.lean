import Rho5.Certificate.B24MinorBridge.Schur
import Rho5.Shared.MinorGrowthThreshold
import Rho5.Shared.TailDeterminant

/-!
# D71 / B24MinorBridge — the D67 minors `A B C D` read at the B24 coordinates

Using only paid identities (D67's `A_eq`/`B_eq`/`C_eq`, D56's `det_eq_prod_delta`) and the
D37 readings of `reconstruct z` from `Schur.lean`:

* `A (reconstruct z) = z 8`;
* `B (reconstruct z) = z 8 * z 0`;
* `C (reconstruct z) = z 8 * z 0 * z 1`;
* `D (reconstruct z) = -z 8 * z 0 * z 1 * z 23`.

No determinant is expanded here: `D` is `M.det` by definition, and the product form is
D56's paid condensation identity `M.det = p M * k M * r M * delta M` evaluated at the
readings above (`delta M = -z 23` from the third/fourth paid steps).  The positivity
hypotheses are exactly the qualification facts `p z > 0`, `z 0 > 0` of the card (plus
`Physical z` for `r z > 0`), never their conclusions.
-/

namespace Rho5.Certificate.B24MinorBridge

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- `A (reconstruct z) = z 8` (the leading `2 × 2` minor is the second pivot reading). -/
theorem A_reconstruct (z : Point) :
    Rho5.MinorGrowthThreshold.A (reconstruct z) = z 8 := by
  rw [Rho5.MinorGrowthThreshold.A_eq (reconstruct z)
      (Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z), p_reconstruct]

/-- `B (reconstruct z) = z 8 * z 0`. -/
theorem B_reconstruct (z : Point) (hp : 0 < Rho5.Certificate.B24Reconstruction.p z) :
    Rho5.MinorGrowthThreshold.B (reconstruct z) = z 8 * z 0 := by
  rw [Rho5.MinorGrowthThreshold.B_eq (reconstruct z)
      (Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z)
      (by rw [p_reconstruct]; exact ne_of_gt hp),
    p_reconstruct, k_reconstruct z (ne_of_gt hp)]

/-- `C (reconstruct z) = z 8 * z 0 * z 1`. -/
theorem C_reconstruct (z : Point) (hp : 0 < Rho5.Certificate.B24Reconstruction.p z)
    (hk : 0 < z 0) :
    Rho5.MinorGrowthThreshold.C (reconstruct z) = z 8 * z 0 * z 1 := by
  rw [Rho5.MinorGrowthThreshold.C_eq (reconstruct z)
      (Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z)
      (by rw [p_reconstruct]; exact hp)
      (by rw [k_reconstruct z (ne_of_gt hp)]; exact hk),
    p_reconstruct, k_reconstruct z (ne_of_gt hp), r_reconstruct z (ne_of_gt hp) (ne_of_gt hk)]

/-- `D (reconstruct z) = -z 8 * z 0 * z 1 * z 23` (D56's condensation at the readings). -/
theorem D_reconstruct (z : Point) (hz : Physical z)
    (hp : 0 < Rho5.Certificate.B24Reconstruction.p z) (hk : 0 < z 0) :
    Rho5.MinorGrowthThreshold.D (reconstruct z) = -z 8 * z 0 * z 1 * z 23 := by
  have hpne : Rho5.Certificate.B24Reconstruction.p z ≠ 0 := ne_of_gt hp
  have hkne : z 0 ≠ 0 := ne_of_gt hk
  have hpM : p (reconstruct z) ≠ 0 := by rw [p_reconstruct]; exact hpne
  have hkM : k (reconstruct z) ≠ 0 := by rw [k_reconstruct z hpne]; exact hkne
  have hrM : r (reconstruct z) ≠ 0 := by
    rw [r_reconstruct z hpne hkne]
    exact ne_of_gt (Rho5.Certificate.B24Reconstruction.r_pos hz)
  rw [Rho5.MinorGrowthThreshold.D,
    Rho5.TailDeterminant.det_eq_prod_delta (reconstruct z)
      (Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero z) hpM hkM hrM,
    p_reconstruct, k_reconstruct z hpne, r_reconstruct z hpne hkne,
    delta_reconstruct z hz hpne hkne]
  ring

end Rho5.Certificate.B24MinorBridge
