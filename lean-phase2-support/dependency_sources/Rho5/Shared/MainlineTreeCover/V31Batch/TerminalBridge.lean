import Rho5.Shared.CertificateRules.ListCheck
import Rho5.Shared.CertificateRules.RealSoundness

/-!
M02 finite payload adapter. The checker and its real soundness are unchanged
D135 imports. List lengths and row widths are retained as explicit payload
qualifications; each actual leaf proves its own check rather than importing a
Boolean from the external transcript. No source-row generation is claimed here.
-/
namespace Rho5.Shared.MainlineTreeCover.V31Batch

open Rho5.Shared.CertificateRules
open Rho5.Shared.CertificateRules.ListCheck
open scoped BigOperators

structure TerminalData where
  lo : List ℤ
  hi : List ℤ
  rows : List (List ℤ)
  rhs : List ℤ
  weights : List ℤ

namespace TerminalData

structure Shape (d : TerminalData) : Prop where
  lohi : d.lo.length = d.hi.length
  rowCount : d.rows.length = d.weights.length
  rhsCount : d.weights.length = d.rhs.length
  rowWidth : ∀ row ∈ d.rows, row.length = d.lo.length

def Ordered (d : TerminalData) : Prop :=
  ∀ j : Fin d.lo.length, d.lo.getD j.val 0 ≤ d.hi.getD j.val 0

def Nonnegative (d : TerminalData) : Prop :=
  ∀ i : Fin d.weights.length, 0 ≤ d.weights.getD i.val 0

def system (d : TerminalData) (h : d.Ordered) :
    LinearSystem (Fin d.weights.length) (Fin d.lo.length) where
  lo := fun j => d.lo.getD j.val 0
  hi := fun j => d.hi.getD j.val 0
  lo_le_hi := h
  rows := fun i j => (d.rows.getD i.val []).getD j.val 0
  rhs := fun i => d.rhs.getD i.val 0

def weightFn (d : TerminalData) : Fin d.weights.length → ℤ :=
  fun i => d.weights.getD i.val 0

def check (d : TerminalData) : Bool :=
  checkL d.lo d.hi d.rows d.rhs d.weights

theorem rhs_eq_list (d : TerminalData) (hs : d.Shape) (ho : d.Ordered) :
    combRhs (d.system ho) d.weightFn = dotL d.weights d.rhs :=
  sum_fin_getD_mul d.weights d.rhs hs.rhsCount

theorem comb_eq_list (d : TerminalData) (hs : d.Shape) (ho : d.Ordered)
    (j : Fin d.lo.length) :
    comb (d.system ho) d.weightFn j = combL d.rows d.weights j.val :=
  sum_fin_rows_eq_combL d.rows d.weights j.val hs.rowCount

theorem min_eq_list (d : TerminalData) (hs : d.Shape) (ho : d.Ordered) :
    boxMin (d.system ho) d.weightFn = boxMinL d.lo d.hi d.rows d.weights := by
  refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_))
    (sum_fin_boxMin d.lo d.hi d.rows d.weights hs.lohi)
  rw [comb_eq_list d hs ho j]
  rfl

theorem check_eq_list (d : TerminalData) (hs : d.Shape) (ho : d.Ordered) :
    nonnegCheck (d.system ho) d.weightFn = d.check := by
  unfold nonnegCheck check checkL
  rw [rhs_eq_list d hs ho, min_eq_list d hs ho]

/-- Real infeasibility of the concrete encoded system. Source lifting is separate. -/
theorem empty_real (d : TerminalData) (hs : d.Shape) (ho : d.Ordered)
    (hw : d.Nonnegative) (hc : d.check = true) :
    ∀ z : Fin d.lo.length → ℝ, ¬ FeasibleR (d.system ho) z := by
  apply nonnegCheck_sound_real (d.system ho) d.weightFn hw
  rw [check_eq_list d hs ho]
  exact hc

/-- A failed new payload check cannot reuse a true check of another payload. -/
theorem rejected_check (d : TerminalData) (h : d.check = false) : d.check ≠ true := by
  rw [h]
  decide

end TerminalData
end Rho5.Shared.MainlineTreeCover.V31Batch
