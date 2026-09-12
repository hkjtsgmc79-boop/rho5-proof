/-
D70 stage 3 — the tail ordering `0 ≤ s M ≤ t M` stated in the original bordered minors,
including the `s = 0` (and `t = 0`) cases, and the ordered-tail witness of the accepted D63.

Paid readings (D62 stage A, all with `M 0 0 = 1` and `0 < p M`, `0 < k M`):

* `m4 M 0 1 = p M * k M * s M`
* `m4 M 1 0 = p M * k M * t M`

so the whole content is the cancellation of the **proved positive** factor `p M * k M`:

* `0 ≤ s M ↔ 0 ≤ m4 M 0 1`,
* `s M ≤ t M ↔ m4 M 0 1 ≤ m4 M 1 0`,
* and therefore `0 ≤ s M ∧ s M ≤ t M ↔ 0 ≤ m4 M 0 1 ∧ m4 M 0 1 ≤ m4 M 1 0`.

No strictness is assumed anywhere: `s M = 0` and `s M = t M = 0` are covered (the two
`…_eq_zero_of_…` readings), and the inequalities are non-strict on both sides.  The last
two theorems only *transport* D63's `exists_ordered_tail_matrix` conclusion into this
minor language, and D59's paid strict branch is recorded with its own explicit hypotheses
(`r M < max (r M) |δ M|`); nothing global or balanced is claimed.
-/
import Rho5.Shared.MinorBoundaryFaces.Equiv
import Rho5.Shared.TailTransposeOrder
import Rho5.Shared.DominantLastPivot

namespace Rho5.MinorBoundaryFaces

open scoped Matrix

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.MinorCPDomain (A B C PolyCP m4)

/-! ## 1. The two tail inequalities, one factor at a time -/

/-- `0 ≤ s M` is exactly `0 ≤ m4 M 0 1` (cancel the proved positive `p M * k M`). -/
theorem s_nonneg_iff_m4_01 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    0 ≤ s M ↔ 0 ≤ m4 M 0 1 := by
  have hck : 0 < p M * k M := mul_pos hp hk
  have h01 : m4 M 0 1 = p M * k M * s M := Rho5.MinorCPDomain.m4_01_eq M h00 hp hk
  constructor
  · intro h
    rw [h01]
    exact mul_nonneg hck.le h
  · intro h
    rw [h01] at h
    exact nonneg_of_mul_nonneg_right h hck

/-- `s M ≤ t M` is exactly `m4 M 0 1 ≤ m4 M 1 0` (same positive factor, no strictness). -/
theorem s_le_t_iff_m4_01_le_m4_10 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) : s M ≤ t M ↔ m4 M 0 1 ≤ m4 M 1 0 := by
  have hck : 0 < p M * k M := mul_pos hp hk
  have h01 : m4 M 0 1 = p M * k M * s M := Rho5.MinorCPDomain.m4_01_eq M h00 hp hk
  have h10 : m4 M 1 0 = p M * k M * t M := Rho5.MinorCPDomain.m4_10_eq M h00 hp hk
  constructor
  · intro h
    rw [h01, h10]
    exact mul_le_mul_of_nonneg_left h hck.le
  · intro h
    rw [h01, h10] at h
    exact le_of_mul_le_mul_left h hck

/-- **The card's ordering equivalence**, both inequalities at once and in the card's
order; non-strict on both sides, so it also covers `s M = 0` and `s M = t M = 0`. -/
theorem tail_ordered_iff_minor_ordered (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) :
    (0 ≤ s M ∧ s M ≤ t M) ↔ (0 ≤ m4 M 0 1 ∧ m4 M 0 1 ≤ m4 M 1 0) :=
  ⟨fun h => ⟨(s_nonneg_iff_m4_01 M h00 hp hk).mp h.1,
      (s_le_t_iff_m4_01_le_m4_10 M h00 hp hk).mp h.2⟩,
    fun h => ⟨(s_nonneg_iff_m4_01 M h00 hp hk).mpr h.1,
      (s_le_t_iff_m4_01_le_m4_10 M h00 hp hk).mpr h.2⟩⟩

/-- The same equivalence with the positivity taken from `PolyCP` (D62's `polyCP_iff_frame`)
instead of being assumed. -/
theorem tail_ordered_iff_minor_ordered_of_polyCP (M : Matrix5) (h00 : M 0 0 = 1)
    (hP : PolyCP M) :
    (0 ≤ s M ∧ s M ≤ t M) ↔ (0 ≤ m4 M 0 1 ∧ m4 M 0 1 ≤ m4 M 1 0) := by
  obtain ⟨-, -, -, -, -, hp, hk, -⟩ := (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hP
  exact tail_ordered_iff_minor_ordered M h00 hp hk

/-! ## 2. The degenerate readings (`s = 0`, `t = 0`), proved, not assumed away -/

/-- A vanishing `s M` gives the vanishing minor `m4 M 0 1` (the `st = 0` case). -/
theorem m4_01_eq_zero_of_s_eq_zero (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hz : s M = 0) : m4 M 0 1 = 0 := by
  rw [Rho5.MinorCPDomain.m4_01_eq M h00 hp hk, hz, mul_zero]

/-- A vanishing `t M` gives the vanishing minor `m4 M 1 0`. -/
theorem m4_10_eq_zero_of_t_eq_zero (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hz : t M = 0) : m4 M 1 0 = 0 := by
  rw [Rho5.MinorCPDomain.m4_10_eq M h00 hp hk, hz, mul_zero]

/-! ## 3. D63's ordered-tail witness, read in minors (transported, not reproved) -/

/-- **Ordered tail in the original minors.**  Under the card's frame hypotheses, D63's
`exists_ordered_tail_matrix` supplies an actual matrix `P` (`P = M` or `P = Mᵀ`, a
whole-matrix transpose) with `0 ≤ s P ≤ t P`; by the equivalence above this is exactly
`0 ≤ m4 P 0 1 ≤ m4 P 1 0`, and `PolyCP P` is re-established from the frame data D63
returns (`p`, `k`, `r` are transpose invariant).  Nothing from D63 is reproved here. -/
theorem exists_ordered_minor_witness (M : Matrix5) (values : List ℝ) (h00 : M 0 0 = 1)
    (hP : PolyCP M) (htrace : Rho5.CompletePivotPath.LegalTrace M values) (hs : 0 ≤ s M)
    (ht : 0 ≤ t M) :
    ∃ P : Matrix5,
      (P = M ∨ P = Mᵀ) ∧ PolyCP P ∧ 0 ≤ m4 P 0 1 ∧ m4 P 0 1 ≤ m4 P 1 0 := by
  obtain ⟨hmax, hcp0, hcp4, hcp3, hcp2, hp, hk, hr⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hP
  obtain ⟨P, hPM, hmaxP, h00P, hcp0P, hcp4P, hcp3P, hcp2P, _htraceP, hsP, hstP, _hgrP⟩ :=
    Rho5.TailTransposeOrder.exists_ordered_tail_matrix M values hmax h00 hcp0 hcp4 hcp3 hcp2
      htrace hs ht
  have hpos : 0 < p P ∧ 0 < k P ∧ 0 < r P := by
    rcases hPM with h | h
    · rw [h]; exact ⟨hp, hk, hr⟩
    · rw [h]
      exact ⟨by rw [Rho5.TailTransposeOrder.p_transpose]; exact hp,
        by rw [Rho5.TailTransposeOrder.k_transpose]; exact hk,
        by rw [Rho5.TailTransposeOrder.r_transpose]; exact hr⟩
  have hpolyP : PolyCP P :=
    (Rho5.MinorCPDomain.polyCP_iff_frame P h00P).mpr
      ⟨hmaxP, hcp0P, hcp4P, hcp3P, hcp2P, hpos.1, hpos.2.1, hpos.2.2⟩
  exact ⟨P, hPM, hpolyP, (tail_ordered_iff_minor_ordered P h00P hpos.1 hpos.2.1).mp
    ⟨hsP, hstP⟩⟩

/-! ## 4. D59's paid dominant strict branch, recorded (not global) -/

/-- **The strict branch in minors.**  With D59's paid hypothesis `r M < max (r M) |δ M|`
(the dominant-last-pivot branch, used exactly as D59 exports it), the tail off-diagonals
are strictly positive, hence so are the two original minors.  This is a conditional record
of D59's branch: it claims nothing global, and it is not a balance statement. -/
theorem strict_branch_minors (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hcpT2 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0) (hr : 0 < r M) (hs : 0 ≤ s M)
    (ht : 0 ≤ t M) (hgt : r M < max (r M) |Rho5.CanonicalTail.delta M|) :
    0 < m4 M 0 1 ∧ 0 < m4 M 1 0 ∧ Rho5.CanonicalTail.delta M < 0 := by
  obtain ⟨hd, -, hs', ht'⟩ :=
    Rho5.DominantLastPivot.strict_tail_of_max_gt_T2 M hcpT2 hr hs ht hgt
  have hck : 0 < p M * k M := mul_pos hp hk
  refine ⟨?_, ?_, hd⟩
  · rw [Rho5.MinorCPDomain.m4_01_eq M h00 hp hk]; exact mul_pos hck hs'
  · rw [Rho5.MinorCPDomain.m4_10_eq M h00 hp hk]; exact mul_pos hck ht'

/-- The same strict branch together with the ordering: `0 < m4 M 0 1 ≤ m4 M 1 0`. -/
theorem strict_branch_minor_ordered (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hcpT2 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0) (hr : 0 < r M)
    (hs : 0 ≤ s M) (ht : 0 ≤ t M) (hgt : r M < max (r M) |Rho5.CanonicalTail.delta M|)
    (hst : s M ≤ t M) : 0 < m4 M 0 1 ∧ m4 M 0 1 ≤ m4 M 1 0 ∧ 0 < m4 M 1 0 := by
  obtain ⟨h1, h2, _⟩ := strict_branch_minors M h00 hp hk hcpT2 hr hs ht hgt
  exact ⟨h1, (s_le_t_iff_m4_01_le_m4_10 M h00 hp hk).mp hst, h2⟩

end Rho5.MinorBoundaryFaces
