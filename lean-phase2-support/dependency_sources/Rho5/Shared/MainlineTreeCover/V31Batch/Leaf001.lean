import Rho5.Shared.MainlineTreeCover.V31Batch.Scaling
import Mathlib.Data.Fintype.Fin

/-!
Actual original C leaf path 000000101, record 11 (0-based).
Raw C SHA256: 1e3988feaa36e043bbb57d7044f7c01f8144b893f7cfb904767be705b51dd10d
Original support IDs and weights are unchanged. The smaller exact lattice uses
T=4800, diagonal T/T^2, common row scale T^2. Exact rational transcription is
recorded separately; source semantics are not assumed from its hash or parser.
-/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Leaf001

open Rho5.Shared.CertificateRules

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def supportIds : List ℕ := [21]

def data : TerminalData where
  lo := [8816, 9918, -9600, -9600, -9600, 636, 318, 4959, 159, 159, 0, 0, -4800, -4800, -4800, -4800, 0, -4800, -4800, -9600, -9600, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, -23040000, -23040000, -23040000, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, 0, 0, 25281, -46080000, -46080000, -46080000, -43027200, -46080000, -43027200, -46080000, 43718544, 2803488, 5606976]
  hi := [9600, 18882, -318, -636, -636, 4800, 4482, 9600, 4800, 4800, 4800, 4800, 0, 0, 0, 0, 4800, 4800, 4800, 0, 0, 0, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 23040000, 23040000, 0, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 0, 23040000, 23040000, 23040000, 0, 0, 0, -202248, -404496, -202248, -404496, 92160000, 43027200, 46080000]
  rows := [
    [7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  rhs := [36864000000]
  weights := [1000000]

theorem dimension : data.lo.length = 57 := by rfl
theorem support_count : data.weights.length = 1 := by rfl
theorem support_ids_valid : supportIds.all (fun i => decide (i < 246)) = true := by decide
theorem support_ids_unique : supportIds.Nodup := by decide

theorem shape : data.Shape := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro row h
    simp only [data, List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | hnil <;> first | rfl | cases hnil

theorem ordered : data.Ordered := by
  intro j
  fin_cases j <;> decide

theorem weights_nonnegative : data.Nonnegative := by
  intro i
  fin_cases i <;> decide

theorem check_true : data.check = true := by decide

/-- Real emptiness of this declared concrete box-row system. -/
theorem empty_real :
    ∀ z : Fin 57 → ℝ, ¬ FeasibleR (data.system ordered) z :=
  data.empty_real shape ordered weights_nonnegative check_true

def coordinateScale (j : Fin 57) : ℚ := if j.val < 22 then 4800 else 23040000

theorem coordinateScale_pos : ∀ j, 0 < coordinateScale j := by
  intro j
  by_cases h : j.val < 22 <;> norm_num [coordinateScale, h]

def rationalSystem : Rational.RatSystem (Fin 1) (Fin 57) :=
  data.scaledSystem ordered coordinateScale coordinateScale_pos (23040000 : ℚ)

/-- The positive diagonal rescaling is proved over real assignments. -/
theorem rational_empty_real : ∀ z : Fin 57 → ℝ, ¬ Rational.FeasibleR rationalSystem z :=
  data.scaled_empty_real shape ordered weights_nonnegative check_true
    coordinateScale coordinateScale_pos (23040000 : ℚ) (by norm_num)

def changedWeightData : TerminalData := { data with weights := [0] }

/-- Setting original support position 0's positive weight to zero fails. -/
theorem changed_weight_rejected : changedWeightData.check = false := by decide

def missingRowData : TerminalData := { data with rows := data.rows.tail }

/-- Dropping a row while retaining the original weights breaks payload shape. -/
theorem missing_row_rejected : ¬ missingRowData.Shape := by
  intro h
  have he := h.rowCount
  norm_num [missingRowData, data] at he

end Rho5.Shared.MainlineTreeCover.V31Batch.Leaf001
