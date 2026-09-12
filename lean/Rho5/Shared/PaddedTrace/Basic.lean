/-
D35 — 完整路径的定长零填充表示（基本层）
==========================================

**卡目标 1.** 定义补零的完整路径关系 `PaddedLegalTrace`（命名空间 `Rho5.PaddedTrace`）：

* `0 × 0`：列表 `[]`；
* 正阶 `n+1`：对**任意**合法主元 `p q`（冻结谓词 `Rho5.Pivot.IsCompletePivot A p q`）
  都可递归，头是真实值 `|A p q|`，尾是 `pivotSchur A p q` 的补零轨迹，
  **没有额外非零前提**。

因此 `A = 0` 时可以在任何合法主元处继续递归并补零——这不是“选定一条固定 tie-break 路径”，
而是把**所有**合法主元选择都纳入关系；原 `LegalTrace` 的 `step`（要求主元非零）与
`zeroStop`（零矩阵立即停）都被覆盖（见 `Bridge.lean` 的双向桥）。

**卡目标 2.** 零矩阵的补零轨迹恰为 `List.replicate n 0`，且存在；原关系的两个真实构造器
`LegalTrace.empty`（`0×0`，值 `[]`）与 `LegalTrace.zeroStop`（正阶零矩阵，值 `[0]`）
在桥接层按原样处理。

复用（只读冻结输入）：D10 `pivotSchur`/`pivotSchur_apply`/零主元⇒零矩阵、
D13 `LegalTrace` 与其结构引理、D17 `tracePeak`/`growthRatio`。本卡不重定义原路径语义。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Mathlib.Data.List.Basic
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath

namespace Rho5.PaddedTrace

open Rho5

/-- **卡目标 1（定义）**：定长零填充的完整合法路径关系。每个合法主元都允许（无 `≠ 0` 前提），
`0 × 0` 终止于 `[]`，每个正阶构造把真实主元值 `|A p q|` 放到头部。 -/
inductive PaddedLegalTrace : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → List ℝ → Prop where
  /-- `0 × 0`：空列表。 -/
  | empty : PaddedLegalTrace (0 : Matrix (Fin 0) (Fin 0) ℝ) []
  /-- 一个合法主元步：头是真实值 `|A p q|`，尾是 Schur 更新的补零轨迹。
  与原 `LegalTrace.step` 的唯一区别是**不要求** `A p q ≠ 0`。 -/
  | step {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (p q : Fin (n + 1))
      (hmax : Rho5.Pivot.IsCompletePivot A p q) {tail : List ℝ}
      (htail : PaddedLegalTrace (Rho5.PivotReindex.pivotSchur A p q) tail) :
      PaddedLegalTrace A (|A p q| :: tail)

/-- **卡目标 1（长度恰为阶数）**：补零轨迹的长度恰好等于矩阵阶数——末端不多加 `0`，
也不允许中途截断。 -/
theorem padded_length : ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {padded : List ℝ},
    PaddedLegalTrace A padded → padded.length = n
  | _, _, _, .empty => rfl
  | _, _, _, .step p q hmax htail => by
      show (|_| :: _).length = _ + 1
      rw [List.length_cons, padded_length htail]

/-- 正阶补零轨迹非空。 -/
theorem padded_ne_nil_of_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {padded : List ℝ} (h : PaddedLegalTrace A padded) : padded ≠ [] := by
  intro hnil
  have := padded_length h
  rw [hnil] at this
  simp at this

/-- 零矩阵的 `pivotSchur` 是零矩阵（`fixedSchur 0 = 0`，实数全除法下也成立）。
本卡局部证明，避免为 3 行事实引入 D32/D26 的拓扑闭包。 -/
theorem pivotSchur_zero {n : ℕ} (p q : Fin (n + 1)) :
    Rho5.PivotReindex.pivotSchur (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q = 0 := by
  ext i j
  rw [Rho5.PivotReindex.pivotSchur_apply]
  simp

/-- **卡目标 2（存在性）**：零矩阵有一条补零轨迹，其值恰为 `List.replicate n 0`。 -/
theorem padded_zero_replicate : ∀ n : ℕ,
    PaddedLegalTrace (0 : Matrix (Fin n) (Fin n) ℝ) (List.replicate n 0)
  | 0 => by simpa using PaddedLegalTrace.empty
  | n + 1 => by
      have htail : PaddedLegalTrace
          (Rho5.PivotReindex.pivotSchur (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0)
          (List.replicate n 0) := by
        rw [pivotSchur_zero]
        exact padded_zero_replicate n
      have h := PaddedLegalTrace.step (A := (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
        0 0 (by intro i j; simp) htail
      simpa [List.replicate_succ] using h

/-- **卡目标 2（唯一性）**：零矩阵的补零轨迹**只能**是 `List.replicate n 0`。 -/
theorem padded_zero_eq_replicate : ∀ {n : ℕ} {padded : List ℝ},
    PaddedLegalTrace (0 : Matrix (Fin n) (Fin n) ℝ) padded → padded = List.replicate n 0
  | _, _, .empty => rfl
  | _, _, .step p q hmax htail => by
      rw [pivotSchur_zero p q] at htail
      rw [padded_zero_eq_replicate htail]
      show |(0 : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ) p q| :: List.replicate _ 0
        = List.replicate (_ + 1) 0
      simp [List.replicate_succ]

/-- **卡目标 2（存在，存在量词形式）**：零矩阵总有补零轨迹。 -/
theorem padded_zero_exists (n : ℕ) :
    ∃ padded : List ℝ, PaddedLegalTrace (0 : Matrix (Fin n) (Fin n) ℝ) padded :=
  ⟨List.replicate n 0, padded_zero_replicate n⟩

/-- 零矩阵补零轨迹的完整刻画（两个方向）。 -/
theorem padded_zero_iff {n : ℕ} {padded : List ℝ} :
    PaddedLegalTrace (0 : Matrix (Fin n) (Fin n) ℝ) padded ↔ padded = List.replicate n 0 :=
  ⟨padded_zero_eq_replicate, fun h => by rw [h]; exact padded_zero_replicate n⟩

end Rho5.PaddedTrace
