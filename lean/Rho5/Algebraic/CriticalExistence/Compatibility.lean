/-
D30 — original-equation compatibility (Instance-dependent tail)
==============================================================

The polynomial, equation, box and `OriginalCritical`/`original_iff` identities were split into
`Rho5.Algebraic.CriticalExistence.Compatibility.Identities` so they can be compiled without the
Jet bounds branch (coordinator instruction, 2026-09-12 02:57).  They are re-exported here
unchanged, so every previously public name keeps working from this module too.

What remains here is the part that genuinely needs the independent existence result from
`Instance`, and therefore both bound branches.
-/
import Rho5.Algebraic.CriticalExistence.Instance
import Rho5.Algebraic.CriticalExistence.Compatibility.Identities

namespace Rho5.Algebraic.CriticalExistence
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 262144

theorem exists_unique_original_critical : ∃! v : Vec, OriginalCritical v := by
  obtain ⟨v,hv,hu⟩ := exists_unique_critical_point
  exact ⟨v,(original_iff v).mpr hv,fun w hw => hu w ((original_iff w).mp hw)⟩

theorem exists_unique_original_system :
    ∃! v : Vec,
      Rho5.Algebraic.CandidateBox (v 0) (v 1) (v 2) (v 3) ∧
      Rho5.Algebraic.P1 (v 0) (v 1) (v 2) (v 3)=0 ∧
      Rho5.Algebraic.P2 (v 0) (v 1) (v 2) (v 3)=0 ∧
      Rho5.Algebraic.P3 (v 0) (v 1) (v 2) (v 3)=0 ∧
      Rho5.Algebraic.J (v 0) (v 1) (v 2) (v 3)=0 :=
  exists_unique_original_critical

theorem criticalPoint_original : OriginalCritical criticalPoint :=
  (original_iff criticalPoint).mpr ⟨criticalPoint_inBox,criticalPoint_isRoot⟩

end
end Rho5.Algebraic.CriticalExistence
