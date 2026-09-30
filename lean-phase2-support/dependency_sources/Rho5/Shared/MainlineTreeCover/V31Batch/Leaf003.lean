import Rho5.Shared.MainlineTreeCover.V31Batch.Scaling
import Mathlib.Data.Fintype.Fin

/-!
Actual original C leaf path 0000001101, record 15 (0-based).
Raw C SHA256: a39db7ea4b129ae1e018347fcf900ba99dbdd75ae15220ede6894eb66264a910
Original support IDs and weights are unchanged. The smaller exact lattice uses
T=4800, diagonal T/T^2, common row scale T^2. Exact rational transcription is
recorded separately; source semantics are not assumed from its hash or parser.
-/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Leaf003

open Rho5.Shared.CertificateRules

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def supportIds : List ℕ := [0, 4, 19, 63, 76, 87, 90, 94, 95, 108, 144, 155, 181, 205, 220, 221, 223, 226]

def data : TerminalData where
  lo := [8816, 9918, -9600, -9600, -9600, 636, 318, 4959, 159, 159, 0, 0, 0, -4800, -4800, -4800, -4800, 0, -4800, -9600, -9600, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, -23040000, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, -23040000, 0, -23040000, 0, 0, 0, 25281, -46080000, -46080000, -46080000, -43027200, -46080000, -43027200, -46080000, 43718544, 2803488, 5606976]
  hi := [9600, 18882, -318, -636, -636, 4800, 4482, 9600, 4800, 4800, 4800, 4800, 4800, 0, 0, 0, 4800, 4800, 0, 0, 0, 0, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 46080000, 0, 23040000, 23040000, 0, 23040000, 23040000, 0, 23040000, 23040000, 0, 23040000, 23040000, 23040000, 23040000, 23040000, 23040000, 0, 0, 0, -202248, -404496, -202248, -404496, 92160000, 43027200, 46080000]
  rows := [
    [0, 0, 0, 0, 0, 0, 0, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [7680000, 0, 0, 0, 0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0],
    [-7680000, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0],
    [0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0],
    [0, -7680000, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -159, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -4482, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -318, 0, 636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 4800, -636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 318, 0, 0, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]]
  rhs := [36864000000, 36864000000, 0, 36864000000, 36864000000, 36864000000, 0, 36864000000, -152340480000, 0, 0, 0, 23040000, -763200, 43027200, 202248, -3052800, -3052800]
  weights := [19, 584, 584, 584, 584, 622, 622, 584, 1206, 933750, 933750, 933750, 933750, 933750, 929050, 1000000, 933750, 995300]

theorem dimension : data.lo.length = 57 := by rfl
theorem support_count : data.weights.length = 18 := by rfl
theorem support_ids_valid : supportIds.all (fun i => decide (i < 246)) = true := by decide
theorem support_ids_unique : supportIds.Nodup := by decide

theorem shape : data.Shape := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro row h
    simp only [data, List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil <;> first | rfl | cases hnil

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

def rationalSystem : Rational.RatSystem (Fin 18) (Fin 57) :=
  data.scaledSystem ordered coordinateScale coordinateScale_pos (23040000 : ℚ)

/-- The positive diagonal rescaling is proved over real assignments. -/
theorem rational_empty_real : ∀ z : Fin 57 → ℝ, ¬ Rational.FeasibleR rationalSystem z :=
  data.scaled_empty_real shape ordered weights_nonnegative check_true
    coordinateScale coordinateScale_pos (23040000 : ℚ) (by norm_num)

def changedWeightData : TerminalData := { data with weights := [19, 0, 584, 584, 584, 622, 622, 584, 1206, 933750, 933750, 933750, 933750, 933750, 929050, 1000000, 933750, 995300] }

/-- Setting original support position 1's positive weight to zero fails. -/
theorem changed_weight_rejected : changedWeightData.check = false := by decide

def missingRowData : TerminalData := { data with rows := data.rows.tail }

/-- Dropping a row while retaining the original weights breaks payload shape. -/
theorem missing_row_rejected : ¬ missingRowData.Shape := by
  intro h
  have he := h.rowCount
  norm_num [missingRowData, data] at he

end Rho5.Shared.MainlineTreeCover.V31Batch.Leaf003
