/-
D56 — 带符号整体行列式与四个加边子式
=====================================

1. **整体带符号行列式**（目标 1）：对实际 `Matrix5 M`，在**纯代数**前提 `M 0 0 = 1`、
   `p M ≠ 0`、`k M ≠ 0` 下

   `det M = p M * k M * (r M * (T2 M 1 1) - s M * t M)`。

   证明只用三次**带符号**首位置 Schur 行列式（D27
   `TraceDeterminant.det_eq_pivot_mul_det_fixedSchur`，分母依次 `M 0 0`、`p M`、`k M`）
   与真实 2×2 行列式（mathlib `Matrix.det_fin_two`），**不**需要 `r M ≠ 0`、完整主元、
   满秩、平衡或任何符号前提；也不引入新的通用行列式定理。
2. **凝聚恒等式**（目标 2）：记 `b_ij = det (D52.borderedMinor M i j)`，则

   `b00*b11 - b01*b10 = p M * k M * det M`，

   直接消费 D52 已付的四个读数（`p*k*r`、`p*k*s`、`p*k*t`、`p*k*d`），保持带符号次序，
   不从绝对行列式反推带符号等号。
3. **接 D48 的 δ**（目标 3）：`r M ≠ 0` 时 `det M = p M * k M * r M * δ M`，从而
   `δ M = det M / (p M * k M * r M)`。
4. **符号资格**（目标 4）：`p M, k M, r M > 0` 时 `det` 与 `δ` 的负/零/正三者等价、
   `det ≠ 0 ↔ δ ≠ 0`，并给出 `δ < 0 ⇒ det < 0 ∧ det ≠ 0` 的直接推论；
   D27 的 `LegalTrace` 零成员判定**只在给定真实迹**时接入，**不**从 `values.length`
   单独推出满秩。

**不声明**：不做 `rho5 = alpha`、全局覆盖、通用 Jacobi 理论或任何四阶/五阶上界。
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.TraceDeterminant
import Rho5.Shared.BorderedTailMinors
import Rho5.Shared.CanonicalTail.Defs

namespace Rho5.TailDeterminant

open Rho5
open Rho5.Certificate.B24Extraction
open Rho5.BorderedTailMinors

/-! ## 0. 首位置 `pivotSchur` 就是冻结的 `fixedSchur` -/

/-- 首位置 `pivotSchur A 0 0` 等于冻结的 `Rho5.Pivot.fixedSchur A`
（`movePivot` 在 `(0,0)` 处是恒等），因此 D27 的带符号行式可直接用在 D37 的
`S4`/`S3`/`T2` 上。 -/
theorem pivotSchur_zero_zero_eq_fixedSchur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Rho5.PivotReindex.pivotSchur A 0 0 = Rho5.Pivot.fixedSchur A := by
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- 反方向，便于把 D27 的公式改写成 D37 的 `S4`/`S3`/`T2`。 -/
theorem fixedSchur_eq_pivotSchur_zero_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Rho5.Pivot.fixedSchur A = Rho5.PivotReindex.pivotSchur A 0 0 :=
  (pivotSchur_zero_zero_eq_fixedSchur A).symm

/-! ## 1. 目标 1：整体带符号行列式 -/

/-- **目标 1（带符号整体行列式）**：`M 0 0 = 1`、`p M ≠ 0`、`k M ≠ 0` 下

`det M = p M * k M * (r M * (T2 M 1 1) - s M * t M)`。

三次带符号 Schur 步（分母 `M 0 0`、`S4 M 0 0 = p M`、`S3 M 0 0 = k M`）把 `det M` 化成
`det (T2 M)`，再用真实 2×2 行列式收尾。全程没有除以 `r M`，故 `r M = 0` 也在域内。 -/
theorem det_eq_prod_tail (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) (hk : k M ≠ 0) :
    M.det = p M * k M * (r M * (T2 M 1 1) - s M * t M) := by
  have h00ne : M 0 0 ≠ 0 := by rw [h00]; exact one_ne_zero
  have hS4 : M.det = M 0 0 * (S4 M).det := by
    have h := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur M h00ne
    rwa [fixedSchur_eq_pivotSchur_zero_zero M] at h
  have hpne : S4 M 0 0 ≠ 0 := hp
  have hS3 : (S4 M).det = S4 M 0 0 * (S3 M).det := by
    have h := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (S4 M) hpne
    rwa [fixedSchur_eq_pivotSchur_zero_zero (S4 M)] at h
  have hkne : S3 M 0 0 ≠ 0 := hk
  have hT2 : (S3 M).det = S3 M 0 0 * (T2 M).det := by
    have h := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (S3 M) hkne
    rwa [fixedSchur_eq_pivotSchur_zero_zero (S3 M)] at h
  have h2 : (T2 M).det = T2 M 0 0 * T2 M 1 1 - T2 M 0 1 * T2 M 1 0 := Matrix.det_fin_two _
  rw [hS4, hS3, hT2, h2, h00, p, k, r, s, t]
  ring

/-! ## 2. 目标 2：四个加边子式的凝聚恒等式 -/

/-- **目标 2（凝聚恒等式）**：`b_ij = det (borderedMinor M i j)` 时

`b00*b11 - b01*b10 = p M * k M * det M`。

证明只做代入：D52 的四个读数给出 `b00 = p*k*r`、`b01 = p*k*s`、`b10 = p*k*t`、
`b11 = p*k*(T2 M 1 1)`，配合目标 1 的带符号 `det M`，环运算即得（保持带符号次序，
不使用任何绝对行列式）。 -/
theorem bordered_condensation (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M 0 0).det * (borderedMinor M 1 1).det
        - (borderedMinor M 0 1).det * (borderedMinor M 1 0).det
      = p M * k M * M.det := by
  rw [det_borderedMinor_00 M h00 hp hk, det_borderedMinor_11 M h00 hp hk,
    det_borderedMinor_01 M h00 hp hk, det_borderedMinor_10 M h00 hp hk,
    det_eq_prod_tail M h00 hp hk]
  ring

/-! ## 3. 目标 3：接 D48 的 δ -/

/-- **目标 3（δ 形式）**：`r M ≠ 0` 时 `det M = p M * k M * r M * δ M`
（`δ M = T2 M 1 1 - t M * s M / r M`，D48 的冻结定义）。这是把目标 1 的
`r*(T2 1 1) - s*t` 提出因子 `r` 的唯一处，因此也是 `r M ≠ 0` 的唯一用处。 -/
theorem det_eq_prod_delta (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) (hk : k M ≠ 0)
    (hr : r M ≠ 0) :
    M.det = p M * k M * r M * Rho5.CanonicalTail.delta M := by
  rw [det_eq_prod_tail M h00 hp hk, Rho5.CanonicalTail.delta]
  field_simp
  try ring

/-- **目标 3（除法形式）**：`δ M = det M / (p M * k M * r M)`。 -/
theorem delta_eq_det_div (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) (hk : k M ≠ 0)
    (hr : r M ≠ 0) :
    Rho5.CanonicalTail.delta M = M.det / (p M * k M * r M) := by
  rw [det_eq_prod_delta M h00 hp hk hr]
  field_simp
  try ring

/-! ## 4. 目标 4：符号资格与 D27 接口 -/

/-- **目标 4（正）**：`p M, k M, r M > 0`（正分母 `p*k*r > 0`）时 `det` 与 `δ` 同为正。 -/
theorem det_pos_iff_delta_pos (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) :
    0 < M.det ↔ 0 < Rho5.CanonicalTail.delta M := by
  rw [det_eq_prod_delta M h00 (ne_of_gt hp) (ne_of_gt hk) (ne_of_gt hr)]
  exact mul_pos_iff_of_pos_left (mul_pos (mul_pos hp hk) hr)

/-- **目标 4（负）**：`p M, k M, r M > 0` 时 `det` 与 `δ` 同为负。 -/
theorem det_neg_iff_delta_neg (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) :
    M.det < 0 ↔ Rho5.CanonicalTail.delta M < 0 := by
  rw [det_eq_prod_delta M h00 (ne_of_gt hp) (ne_of_gt hk) (ne_of_gt hr)]
  constructor
  · intro h
    by_contra hcon
    have h2 : 0 ≤ Rho5.CanonicalTail.delta M := le_of_not_gt hcon
    have h3 : 0 ≤ p M * k M * r M * Rho5.CanonicalTail.delta M :=
      mul_nonneg (le_of_lt (mul_pos (mul_pos hp hk) hr)) h2
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hp hk) hr) h

/-- **目标 4（零）**：`p M, k M, r M > 0` 时 `det M = 0 ↔ δ M = 0`。 -/
theorem det_eq_zero_iff_delta_eq_zero (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) :
    M.det = 0 ↔ Rho5.CanonicalTail.delta M = 0 := by
  rw [det_eq_prod_delta M h00 (ne_of_gt hp) (ne_of_gt hk) (ne_of_gt hr)]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (mul_pos (mul_pos hp hk) hr))
  · intro h
    rw [h, mul_zero]

/-- **目标 4（非零）**：`p M, k M, r M > 0` 时 `det M ≠ 0 ↔ δ M ≠ 0`。 -/
theorem det_ne_zero_iff_delta_ne_zero (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) :
    M.det ≠ 0 ↔ Rho5.CanonicalTail.delta M ≠ 0 := by
  rw [det_eq_prod_delta M h00 (ne_of_gt hp) (ne_of_gt hk) (ne_of_gt hr)]
  constructor
  · intro h hd
    exact h (by rw [hd, mul_zero])
  · intro h hd
    exact h ((mul_eq_zero.mp hd).resolve_left (ne_of_gt (mul_pos (mul_pos hp hk) hr)))

/-- **目标 4（下游尾分支直接推论）**：`δ M < 0` 时 `det M < 0` 且 `det M ≠ 0`。 -/
theorem det_neg_of_delta_neg (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hr : 0 < r M) (hdelta : Rho5.CanonicalTail.delta M < 0) :
    M.det < 0 ∧ M.det ≠ 0 := by
  have hneg : M.det < 0 := (det_neg_iff_delta_neg M h00 hp hk hr).mpr hdelta
  exact ⟨hneg, ne_of_lt hneg⟩

/-- **D27 接口（只在给定真实迹时）**：对任意真实 `LegalTrace M values`，
`det M ≠ 0 ↔ 0 ∉ values`（D27 冻结判定，本卡只做搬运）。 -/
theorem det_ne_zero_iff_zero_not_mem_of_trace {M : Matrix5} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace M values) :
    M.det ≠ 0 ↔ 0 ∉ values :=
  Rho5.TraceDeterminant.det_ne_zero_iff_zero_not_mem h

/-- **D27 接口 + δ**：给定真实迹与正分母时 `δ M ≠ 0 ↔ 0 ∉ values`。
注意这里**没有**从 `values.length` 单独推出满秩或 `det ≠ 0` 的陈述。 -/
theorem delta_ne_zero_iff_zero_not_mem_of_trace {M : Matrix5} {values : List ℝ}
    (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M)
    (h : Rho5.CompletePivotPath.LegalTrace M values) :
    Rho5.CanonicalTail.delta M ≠ 0 ↔ 0 ∉ values :=
  (det_ne_zero_iff_delta_ne_zero M h00 hp hk hr).symm.trans
    (det_ne_zero_iff_zero_not_mem_of_trace h)

end Rho5.TailDeterminant
