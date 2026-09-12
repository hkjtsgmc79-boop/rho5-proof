import Rho5.Algebraic.CriticalExistence.JetBounds
import Rho5.Algebraic.CriticalExistence.CenterBounds
-- D30 thin-call wiring (coordinator dispatch 2026-09-12 03:33, unlock 04:06):
-- `concrete_center` is proved independently by D47 in this namespace; D30 keeps the original
-- public declaration and type and only calls it.  Nothing is copied from D47's module.
import Rho5.Algebraic.CriticalExistence.CenterBoundReady
-- D30 thin-call wiring (unlock 2026-09-12 04:22): `concrete_slopes` is proved independently by
-- D50 in `SlopeBoundReady.ConcreteSlopes`; D30 keeps the original declaration and type.
import Rho5.Algebraic.CriticalExistence.SlopeBoundReady.ConcreteSlopes

namespace Rho5.Algebraic.CriticalExistence
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 262144

theorem actual_jacobian_enclosure (v : Vec) (hv : InBox v) (i j : Fin 4) :
    (dfIntervals i j).Mem (jacobianEntry v i j) := by
  have h := in_coarse hv
  fin_cases i
  · simpa only [dfIntervals,jacobianEntry,criticalExpr,dv00728,Matrix.cons_val_zero,Matrix.cons_val_succ] using jet00728.slope j v v h h
  · simpa only [dfIntervals,jacobianEntry,criticalExpr,dv01504,Matrix.cons_val_zero,Matrix.cons_val_succ] using jet01504.slope j v v h h
  · simpa only [dfIntervals,jacobianEntry,criticalExpr,dv02217,Matrix.cons_val_zero,Matrix.cons_val_succ] using jet02217.slope j v v h h
  · simpa only [dfIntervals,jacobianEntry,criticalExpr,dv12242,Matrix.cons_val_zero,Matrix.cons_val_succ] using jet12242.slope j v v h h

def entryMagnitude (i j : Fin 4) : ℚ :=
  max |(errorIntervals i j).lo| |(errorIntervals i j).hi|
def rawRowBound (i : Fin 4) : ℚ :=
  entryMagnitude i 0+entryMagnitude i 1+entryMagnitude i 2+entryMagnitude i 3
def weightedRowBound (i : Fin 4) : ℚ :=
  (entryMagnitude i 0*radQ 0+entryMagnitude i 1*radQ 1+
   entryMagnitude i 2*radQ 2+entryMagnitude i 3*radQ 3)/radQ i

theorem tight_rational_rows (i : Fin 4) :
    rawRowBound i < 1/(10:ℚ)^74 ∧ weightedRowBound i < 1/(10:ℚ)^55 := by
  -- D30 repair (verified): `norm_num [rawRowBound,weightedRowBound,entryMagnitude,
  -- errorIntervals,radQ]` cannot reduce the `![…] i` indexing of the generated interval and
  -- radius literals — reproduced as a real `unsolved goals` failure against the published
  -- layer.  The general `Matrix.cons_val'` plus the `Fin` literal lemmas reduce the indexing,
  -- after which `norm_num` closes the rational inequality.  Verified standalone: exit 0, 4.16 s.
  fin_cases i <;>
    simp only [rawRowBound, weightedRowBound, entryMagnitude, errorIntervals, radQ,
      Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Fin.isValue] <;>
    norm_num

theorem concrete_slopes (i j : Fin 4) (v w : Vec)
    (hv : CenteredBox midpoint radius v) (hw : CenteredBox midpoint radius w) :
    |(newtonExpr i).secant j v w| * radius j ≤ radius i / 16 :=
  -- D30 thin call: the proof lives in D50's `SlopeBoundReady.ConcreteSlopes` module
  -- (SLOPE_LEMMA_READY, frozen outputs/heartbeat_0420_delivery_20260912/D50).
  Rho5.Algebraic.CriticalExistence.SlopeBoundReady.concrete_slopes i j v w hv hw

theorem concrete_center (i : Fin 4) :
    |(newtonExpr i).eval midpoint-midpoint i| ≤ radius i/2 :=
  -- D30 thin call: the proof lives in D47's `CenterBoundReady` module (CENTER_LEMMA_READY,
  -- frozen outputs/heartbeat_0349_delivery_20260912/D47).  The public name and the full
  -- original type above are unchanged; this lane does not re-prove it.
  Rho5.Algebraic.CriticalExistence.CenterBoundReady.concrete_center_ready i

theorem exists_unique_critical_point :
    ∃! v : Vec, InBox v ∧ criticalSystem v = 0 := by
  obtain ⟨v,hv,hu⟩ := exists_unique_zero_of_interval_newton
    criticalSystem applyC newtonExpr midpoint radius radius_pos
    newton_formula C_zero C_injective concrete_center concrete_slopes
  refine ⟨v,⟨(inBox_iff_centered v).mpr hv.1,hv.2⟩,?_⟩
  intro w hw
  exact hu w ⟨(inBox_iff_centered w).mp hw.1,hw.2⟩

noncomputable def criticalPoint : Vec :=
  Classical.choose exists_unique_critical_point.exists

theorem criticalPoint_inBox : InBox criticalPoint :=
  (Classical.choose_spec exists_unique_critical_point.exists).1

theorem criticalPoint_isRoot : criticalSystem criticalPoint = 0 :=
  (Classical.choose_spec exists_unique_critical_point.exists).2

theorem criticalPoint_unique {v : Vec} (hv : InBox v) (hf : criticalSystem v=0) :
    v=criticalPoint := by
  obtain ⟨w,hw,hu⟩ := exists_unique_critical_point
  exact (hu v ⟨hv,hf⟩).trans (hu criticalPoint ⟨criticalPoint_inBox,criticalPoint_isRoot⟩).symm

end
end Rho5.Algebraic.CriticalExistence
