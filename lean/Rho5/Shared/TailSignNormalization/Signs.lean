/-
D53 — 末位行/列符号向量（真实 D22 `signedEntries` 的符号数据）
=================================================================

本模块只提供**符号数据本身**：在阶 5/4/3/2 上「除最后一位为 `ε` 外全为 `1`」的符号向量，
以及它们的 `IsSign` 资格、逐条目求值与**逐阶尾限制**恒等式（`sigma5` 的 `succ` 尾恰是
`sigma4`，等等）。这些正是 D22 `signedEntries` 的输入，本卡不发明第二套符号语义。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceSigns.Trace
import Rho5.Shared.TraceSigns.GrowthAdapter

namespace Rho5.TailSignNormalization

open Rho5

/-- 阶 5 末位符号：原矩阵下标 `4` 取 `ε`，其余取 `1`。 -/
noncomputable def sigma5 (ε : ℝ) : Fin 5 → ℝ := fun i => if (i : ℕ) = 4 then ε else 1

/-- 阶 4 末位符号（`sigma5` 的 `succ` 尾）。 -/
noncomputable def sigma4 (ε : ℝ) : Fin 4 → ℝ := fun i => if (i : ℕ) = 3 then ε else 1

/-- 阶 3 末位符号。 -/
noncomputable def sigma3 (ε : ℝ) : Fin 3 → ℝ := fun i => if (i : ℕ) = 2 then ε else 1

/-- 阶 2 末位符号。 -/
noncomputable def sigma2 (ε : ℝ) : Fin 2 → ℝ := fun i => if (i : ℕ) = 1 then ε else 1

/-! ## `IsSign` 资格（`ε = ±1`） -/

theorem isSign_sigma5 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Rho5.TraceSigns.IsSign (sigma5 ε) := by
  intro i
  by_cases h : (i : ℕ) = 4
  · rcases hε with rfl | rfl <;> simp [sigma5, h]
  · simp [sigma5, h]

theorem isSign_sigma4 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Rho5.TraceSigns.IsSign (sigma4 ε) := by
  intro i
  by_cases h : (i : ℕ) = 3
  · rcases hε with rfl | rfl <;> simp [sigma4, h]
  · simp [sigma4, h]

theorem isSign_sigma3 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Rho5.TraceSigns.IsSign (sigma3 ε) := by
  intro i
  by_cases h : (i : ℕ) = 2
  · rcases hε with rfl | rfl <;> simp [sigma3, h]
  · simp [sigma3, h]

theorem isSign_sigma2 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Rho5.TraceSigns.IsSign (sigma2 ε) := by
  intro i
  by_cases h : (i : ℕ) = 1
  · rcases hε with rfl | rfl <;> simp [sigma2, h]
  · simp [sigma2, h]

/-! ## 逐条目求值 -/

@[simp] theorem sigma5_zero (ε : ℝ) : sigma5 ε 0 = 1 := by simp [sigma5]
@[simp] theorem sigma5_last (ε : ℝ) : sigma5 ε 4 = ε := by simp [sigma5]
@[simp] theorem sigma4_zero (ε : ℝ) : sigma4 ε 0 = 1 := by simp [sigma4]
@[simp] theorem sigma4_last (ε : ℝ) : sigma4 ε 3 = ε := by simp [sigma4]
@[simp] theorem sigma3_zero (ε : ℝ) : sigma3 ε 0 = 1 := by simp [sigma3]
@[simp] theorem sigma3_last (ε : ℝ) : sigma3 ε 2 = ε := by simp [sigma3]
@[simp] theorem sigma2_zero (ε : ℝ) : sigma2 ε 0 = 1 := by simp [sigma2]
@[simp] theorem sigma2_last (ε : ℝ) : sigma2 ε 1 = ε := by simp [sigma2]

/-! ## 逐阶尾限制恒等式 -/

theorem tail_sigma5 (ε : ℝ) : (fun i : Fin 4 => sigma5 ε i.succ) = sigma4 ε := by
  funext i
  have hiff : ((i.succ : ℕ) = 4) ↔ ((i : ℕ) = 3) := by
    show (i : ℕ) + 1 = _ + 1 ↔ (i : ℕ) = _
    exact Nat.add_right_cancel_iff
  simp only [sigma5, sigma4, hiff]

theorem tail_sigma4 (ε : ℝ) : (fun i : Fin 3 => sigma4 ε i.succ) = sigma3 ε := by
  funext i
  have hiff : ((i.succ : ℕ) = 3) ↔ ((i : ℕ) = 2) := by
    show (i : ℕ) + 1 = _ + 1 ↔ (i : ℕ) = _
    exact Nat.add_right_cancel_iff
  simp only [sigma4, sigma3, hiff]

theorem tail_sigma3 (ε : ℝ) : (fun i : Fin 2 => sigma3 ε i.succ) = sigma2 ε := by
  funext i
  have hiff : ((i.succ : ℕ) = 2) ↔ ((i : ℕ) = 1) := by
    show (i : ℕ) + 1 = _ + 1 ↔ (i : ℕ) = _
    exact Nat.add_right_cancel_iff
  simp only [sigma3, sigma2, hiff]

end Rho5.TailSignNormalization
