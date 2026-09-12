/-
D52 — 2×2 Schur 尾的四个真实加边子式
=====================================

卡目标：把固定的二阶 `Schur` 尾坐标读成**真实 4×4 加边子式的行列式**（无分母的证书桥）。

固定 `M : Matrix5`。唯一局部辅助嵌入

`embed (i : Fin 2) : Fin 4 → Fin 5`，有序下标 `[0,1,2,3+i]`

（即 `embed 0` 丢掉原始下标 `4`，`embed 1` 丢掉原始下标 `3`），加边子式

`borderedMinor M i j := M.submatrix (embed i) (embed j)`。

交付：

1. `borderedMinor M 0 0 = Rho5.LeadingMinorFour.A4 M`（D49 的实际导出名）；
2. 在**纯代数**前提 `M 0 0 = 1`、`p M ≠ 0`、`k M ≠ 0` 下，对 `i j : Fin 2` **一致地**

   `det (borderedMinor M i j) = p M * k M * T2 M i j`；

   没有任何完整主元 / 平衡尾 / 满秩 / `r M ≠ 0` 假设；行列式符号与行/列次序原样保留；
3. 四个读数 `p*k*r`、`p*k*s`、`p*k*t`、`p*k*T2 M 1 1`（`d` 即 `T2 M 1 1`，
   **不是** D37 图表坐标 `z 7 = S3 M 2 0 / k M`）；
4. `p M > 0`、`k M > 0`（"positive denominator"）时尾条目与对应子式的**符号等价**，
   以及除法形式 `T2 M i j = det (borderedMinor M i j) / (p M * k M)`。

**不声明**：不证明 `rho5 = alpha`、不证明全局平衡尾、不做任何固定坐标以外的推广；
不引入通用嵌入 / 任意维子矩阵框架。

实现路线（全部为固定尺寸）：D27 的**带符号** Schur 行列式公式
`TraceDeterminant.det_eq_pivot_mul_det_fixedSchur`（`det A = A 0 0 * det (fixedSchur A)`，
`A 0 0 ≠ 0`）连续三次，把 `det (borderedMinor M i j)` 化成末级 1×1 的条目；每一步的角条目
由逐条目公式与 D37 的 `S4_apply`/`S3_apply`/`T2_apply` 对上。只用绝对值形式（例如
`abs_det_eq_prod`）不足以给出带符号等号，故此处**只**用带符号公式。

只读复用：D08/D10/D13（`fixedSchur`/`pivotSchur`）、D27 `TraceDeterminant`、
D37 `Certificate.B24Extraction.Extract`（`S4`/`S3`/`T2`/`p`/`k`/`r`/`s`/`t`）、
D49 `LeadingMinorFour`（`A4`）。无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.TraceDeterminant
import Rho5.Shared.LeadingMinorFour
import Rho5.Certificate.B24Extraction.Extract

namespace Rho5.BorderedTailMinors

open Rho5
open Rho5.Certificate.B24Extraction

/-! ## 0. 固定有序嵌入与四个加边子式 -/

/-- **卡固定的有序嵌入**：`embed 0 = [0,1,2,3]`（丢下标 `4`），`embed 1 = [0,1,2,4]`
（丢下标 `3`），即下标 `[0,1,2,3+i]`。只做这两个固定层，不建立任意嵌入框架。 -/
def embed (i : Fin 2) : Fin 4 → Fin 5
  | 0 => 0
  | 1 => (0 : Fin 4).succ
  | 2 => (1 : Fin 4).succ
  | 3 => i.succ.succ.succ

/-- 嵌入在下标 `0` 处的值（两种 `i` 都是 `0`）。 -/
@[simp] theorem embed_zero (i : Fin 2) : embed i 0 = 0 := rfl

/-- 嵌入在下标 `1` 处的值（两种 `i` 都是 `1`）。 -/
@[simp] theorem embed_one (i : Fin 2) : embed i 1 = 1 := rfl

/-- 嵌入在下标 `2` 处的值（两种 `i` 都是 `2`）。 -/
@[simp] theorem embed_two (i : Fin 2) : embed i 2 = 2 := rfl

/-- 嵌入在被跳过的下标 `3` 处的值：`3 + i`。 -/
@[simp] theorem embed_three (i : Fin 2) : embed i 3 = i.succ.succ.succ := rfl

/-- **卡固定的加边子式**：`borderedMinor M i j = M.submatrix (embed i) (embed j)`，
即删去第 `4-i` 行与第 `4-j` 列后的有序 4×4 子式。 -/
def borderedMinor (M : Matrix5) (i j : Fin 2) : Matrix (Fin 4) (Fin 4) ℝ :=
  M.submatrix (embed i) (embed j)

/-- 加边子式的逐条目读法。 -/
theorem borderedMinor_apply (M : Matrix5) (i j : Fin 2) (a b : Fin 4) :
    borderedMinor M i j a b = M (embed i a) (embed j b) := rfl

/-- **卡目标（`i = j = 0` 是 D49 的左上 4×4）**：`borderedMinor M 0 0 = A4 M`，
用的是 D49 实际导出的名字 `Rho5.LeadingMinorFour.A4`。 -/
theorem borderedMinor_zero_zero (M : Matrix5) :
    borderedMinor M 0 0 = Rho5.LeadingMinorFour.A4 M := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [borderedMinor, embed, Rho5.LeadingMinorFour.A4]

/-- 四个加边子式的角条目都还是 `M 0 0`（嵌入保 `0`）。 -/
theorem borderedMinor_zero_zero_entry (M : Matrix5) (i j : Fin 2) :
    borderedMinor M i j 0 0 = M 0 0 := by
  simp [borderedMinor]

/-! ## 1. 固定层的逐条目公式与下标桥 -/

/-- 冻结 `fixedSchur` 的逐条目公式（`rfl`，只在此卡固定的 4→3、3→2、2→1 层上使用）。 -/
theorem fixedSchur_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a b : Fin n) :
    Rho5.Pivot.fixedSchur A a b = A a.succ b.succ - A a.succ 0 * A 0 b.succ / A 0 0 := rfl

/-- 下标桥：`(0 : Fin 3).succ = 1`（用作 `simp` 规则，把展开后的 `Fin.succ` 形式归一）。 -/
@[simp] theorem succ_fin3_zero : ((0 : Fin 3).succ : Fin 4) = 1 := by decide
/-- 下标桥：`(1 : Fin 3).succ = 2`。 -/
@[simp] theorem succ_fin3_one : ((1 : Fin 3).succ : Fin 4) = 2 := by decide
/-- 下标桥：`(0 : Fin 2).succ = 1`。 -/
@[simp] theorem succ_fin2_zero : ((0 : Fin 2).succ : Fin 3) = 1 := by decide
/-- 下标桥：`(1 : Fin 2).succ = 2`。 -/
@[simp] theorem succ_fin2_one : ((1 : Fin 2).succ : Fin 3) = 2 := by decide
/-- 下标桥：`(0 : Fin 1).succ = 1`（末级 2×2 → 1×1 的消元下标）。 -/
@[simp] theorem succ_fin1_zero : ((0 : Fin 1).succ : Fin 2) = 1 := by decide

/-! ## 2. 层 5→4：`borderedMinor M i j` 的 Schur 条目对上 `S4 M` -/

/-- **层 5→4，条目 `(0,0)`**：限制到加边子式后第一次首位置消元的角条目就是 `S4 M 0 0 = p M`。 -/
theorem schur_borderedMinor_00 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 0 0 = S4 M 0 0 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(0,1)`**。 -/
theorem schur_borderedMinor_01 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 0 1 = S4 M 0 1 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(1,0)`**。 -/
theorem schur_borderedMinor_10 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 1 0 = S4 M 1 0 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(1,1)`**。 -/
theorem schur_borderedMinor_11 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 1 1 = S4 M 1 1 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(0,2)`**：列方向用到了被跳过的列下标，故依赖 `j`。 -/
theorem schur_borderedMinor_02 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 0 2 = S4 M 0 j.succ.succ := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(2,0)`**：行方向用到了被跳过的行下标，故依赖 `i`。 -/
theorem schur_borderedMinor_20 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 2 0 = S4 M i.succ.succ 0 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(2,1)`**。 -/
theorem schur_borderedMinor_21 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 2 1 = S4 M i.succ.succ 1 := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(1,2)`**。 -/
theorem schur_borderedMinor_12 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 1 2 = S4 M 1 j.succ.succ := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-- **层 5→4，条目 `(2,2)`**：行、列方向都用到被跳过的下标，故同时依赖 `i` 与 `j`。 -/
theorem schur_borderedMinor_22 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (borderedMinor M i j) 2 2 = S4 M i.succ.succ j.succ.succ := by
  simp only [Rho5.Pivot.fixedSchur, borderedMinor, Matrix.submatrix_apply, embed, S4_apply,
    Fin.succ]
  try ring

/-! ## 3. 层 4→3：第二次消元的条目对上 `S3 M` -/

/-- **层 4→3，条目 `(0,0)`**：`S3 M 0 0 = k M`。 -/
theorem schur₂_borderedMinor_00 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)) 0 0 = S3 M 0 0 := by
  rw [fixedSchur_apply]
  simp only [succ_fin2_zero]
  rw [schur_borderedMinor_11 M i j, schur_borderedMinor_10 M i j,
    schur_borderedMinor_01 M i j, schur_borderedMinor_00 M i j, S3_apply]
  try simp only [succ_fin3_zero]
  try ring

/-- **层 4→3，条目 `(1,1)`**：依赖 `i`、`j`（被跳过的行/列下标）。 -/
theorem schur₂_borderedMinor_11 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)) 1 1
      = S3 M i.succ j.succ := by
  rw [fixedSchur_apply]
  simp only [succ_fin2_one]
  rw [schur_borderedMinor_22 M i j, schur_borderedMinor_20 M i j,
    schur_borderedMinor_02 M i j, schur_borderedMinor_00 M i j, S3_apply]
  try simp only [succ_fin3_zero]
  try ring

/-- **层 4→3，条目 `(1,0)`**。 -/
theorem schur₂_borderedMinor_10 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)) 1 0
      = S3 M i.succ 0 := by
  rw [fixedSchur_apply]
  simp only [succ_fin2_one, succ_fin2_zero]
  rw [schur_borderedMinor_21 M i j, schur_borderedMinor_20 M i j,
    schur_borderedMinor_01 M i j, schur_borderedMinor_00 M i j, S3_apply]
  try simp only [succ_fin3_zero]
  try ring

/-- **层 4→3，条目 `(0,1)`**。 -/
theorem schur₂_borderedMinor_01 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)) 0 1
      = S3 M 0 j.succ := by
  rw [fixedSchur_apply]
  simp only [succ_fin2_one, succ_fin2_zero]
  rw [schur_borderedMinor_12 M i j, schur_borderedMinor_10 M i j,
    schur_borderedMinor_02 M i j, schur_borderedMinor_00 M i j, S3_apply]
  try simp only [succ_fin3_zero]
  try ring

/-! ## 4. 层 3→2：末级 1×1 的条目就是 `T2 M i j` -/

/-- **层 3→2（末级）**：第三次消元后只剩 1×1，其条目正是真实 `T2 M i j`；
`T2 M i j` 的下标恰为两个被跳过的原始下标之差，因此不需要任何额外假设。 -/
theorem schur₃_borderedMinor_00 (M : Matrix5) (i j : Fin 2) :
    Rho5.Pivot.fixedSchur
        (Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j))) 0 0
      = T2 M i j := by
  rw [fixedSchur_apply]
  simp only [succ_fin1_zero]
  rw [schur₂_borderedMinor_11 M i j, schur₂_borderedMinor_10 M i j,
    schur₂_borderedMinor_01 M i j, schur₂_borderedMinor_00 M i j, T2_apply]
  try simp only [succ_fin2_one]
  try ring

/-! ## 5. 主定理：`det (borderedMinor M i j) = p M * k M * T2 M i j` -/

/-- **卡主定理（无分母证书桥）**：纯代数前提 `M 0 0 = 1`、`p M ≠ 0`、`k M ≠ 0` 下，
对 **所有** `i j : Fin 2` 一致地

`det (borderedMinor M i j) = p M * k M * T2 M i j`。

证明只用 **带符号** 的 D27 Schur 行列式公式三次（`M 0 0 ≠ 0`、`p M ≠ 0`、`k M ≠ 0`
分别是三次消元的分母条件），再到 1×1 的 `det = 条目`；没有完整主元、平衡尾、满秩或
`r M ≠ 0` 假设，也没有绝对值化的行列式步骤。 -/
theorem det_borderedMinor (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M i j).det = p M * k M * T2 M i j := by
  have h00ne : M 0 0 ≠ 0 := by rw [h00]; exact one_ne_zero
  have hA := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (borderedMinor M i j)
    (by rw [borderedMinor_zero_zero_entry]; exact h00ne)
  have hpne : Rho5.Pivot.fixedSchur (borderedMinor M i j) 0 0 ≠ 0 := by
    rw [schur_borderedMinor_00]; exact hp
  have hB := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur
    (Rho5.Pivot.fixedSchur (borderedMinor M i j)) hpne
  have hkne : Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)) 0 0 ≠ 0 := by
    rw [schur₂_borderedMinor_00]; exact hk
  have hC := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur
    (Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j))) hkne
  have hD : (Rho5.Pivot.fixedSchur
        (Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j)))).det
      = Rho5.Pivot.fixedSchur
        (Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (borderedMinor M i j))) 0 0 :=
    Matrix.det_fin_one _
  rw [hA, borderedMinor_zero_zero_entry, hB, schur_borderedMinor_00, hC,
    schur₂_borderedMinor_00, hD, schur₃_borderedMinor_00, h00, p, k]
  try ring

/-! ## 6. 四个读数与符号桥 -/

/-- **读数 `p*k*r`**：`det (borderedMinor M 0 0) = p M * k M * r M`（`r M = T2 M 0 0`）。 -/
theorem det_borderedMinor_00 (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M 0 0).det = p M * k M * r M := by
  rw [det_borderedMinor M 0 0 h00 hp hk]
  rfl

/-- **读数 `p*k*s`**：`det (borderedMinor M 0 1) = p M * k M * s M`（`s M = T2 M 0 1`）。 -/
theorem det_borderedMinor_01 (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M 0 1).det = p M * k M * s M := by
  rw [det_borderedMinor M 0 1 h00 hp hk]
  rfl

/-- **读数 `p*k*t`**：`det (borderedMinor M 1 0) = p M * k M * t M`（`t M = T2 M 1 0`）。 -/
theorem det_borderedMinor_10 (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M 1 0).det = p M * k M * t M := by
  rw [det_borderedMinor M 1 0 h00 hp hk]
  rfl

/-- **读数 `p*k*d`**：这里的 `d` 就是 **`T2 M 1 1`**（尾块对角元），
**不是** D37 图表里的坐标 `z 7 = S3 M 2 0 / k M`。 -/
theorem det_borderedMinor_11 (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    (borderedMinor M 1 1).det = p M * k M * T2 M 1 1 :=
  det_borderedMinor M 1 1 h00 hp hk

/-- **除法形式（分母 `p M * k M`）**：把无分母等式改写成尾坐标的商。 -/
theorem tail_entry_eq_det_div (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1)
    (hp : p M ≠ 0) (hk : k M ≠ 0) :
    T2 M i j = (borderedMinor M i j).det / (p M * k M) := by
  rw [det_borderedMinor M i j h00 hp hk]
  exact (mul_div_cancel_left₀ _ (mul_ne_zero hp hk)).symm

/-- **符号等价（正）**：`p M > 0`、`k M > 0` 时（正分母）尾条目与对应子式同号；
此处给出严格正部分。 -/
theorem tail_entry_pos_iff_det_pos (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) :
    0 < T2 M i j ↔ 0 < (borderedMinor M i j).det := by
  rw [det_borderedMinor M i j h00 (ne_of_gt hp) (ne_of_gt hk)]
  exact (mul_pos_iff_of_pos_left (mul_pos hp hk)).symm

/-- **符号等价（负）**：正分母下严格负部分。 -/
theorem tail_entry_neg_iff_det_neg (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) :
    T2 M i j < 0 ↔ (borderedMinor M i j).det < 0 := by
  rw [det_borderedMinor M i j h00 (ne_of_gt hp) (ne_of_gt hk)]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg (mul_pos hp hk) h
  · intro h
    by_contra hcon
    have h2 : 0 ≤ T2 M i j := le_of_not_gt hcon
    have h3 : 0 ≤ p M * k M * T2 M i j := mul_nonneg (le_of_lt (mul_pos hp hk)) h2
    linarith

/-- **符号等价（零）**：正分母下消失部分（`p M * k M ≠ 0`）。 -/
theorem tail_entry_eq_zero_iff_det_eq_zero (M : Matrix5) (i j : Fin 2) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) :
    T2 M i j = 0 ↔ (borderedMinor M i j).det = 0 := by
  rw [det_borderedMinor M i j h00 (ne_of_gt hp) (ne_of_gt hk)]
  exact ⟨fun h => by rw [h, mul_zero],
    fun h => (mul_eq_zero.mp h).resolve_left (mul_ne_zero (ne_of_gt hp) (ne_of_gt hk))⟩

end Rho5.BorderedTailMinors
