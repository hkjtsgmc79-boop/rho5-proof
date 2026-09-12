/-
D35 — 原 `LegalTrace` 与定长补零轨迹的双向桥
=============================================

**卡目标 3.** 对任意 `n`、`A : Matrix (Fin n) (Fin n) ℝ` 与列表 `padded`：

  `PaddedLegalTrace A padded ↔ ∃ values, LegalTrace A values ∧ padded = padList n values`

其中 `padList n values = values ++ List.replicate (n - values.length) 0`。
两个方向都是真证明：

* `⟸`（原路径 → 补零）：对 `LegalTrace` 结构递归。`empty`（`0×0`，`values = []`）与
  `zeroStop`（正阶零矩阵，`values = [0]`）按**真实构造器**分别处理：`zeroStop` 的补零
  恰是零矩阵的 `replicate` 轨迹（目标 2）；`step` 情形把非零主元这一步交给
  `PaddedLegalTrace.step`（它不要求非零，故成立），尾用归纳假设。
* `⟹`（补零 → 原路径）：对补零轨迹结构递归。若该步主元非零，就是原 `step`；
  若主元为零，由 D10 `eq_zero_of_isCompletePivot_of_pivot_eq_zero` 得 `A = 0`，
  此时补零尾必为 `replicate n 0`（目标 2 的唯一性），原路径取 `zeroStop`（值 `[0]`），
  补零后正好是 `|0| :: replicate n 0`。

**不假定所有原路径都满长**：`padList` 用 `n - values.length` 补零，并引用 D13 的
`length_le` 保证指数正确；奇异矩阵（提前 `zeroStop`）与全部并列主元选择都被覆盖——
桥对**给定**的任意一条原路径成立，反之补零轨迹给出**某一条**原路径。
-/
import Rho5.Shared.PaddedTrace.Basic

namespace Rho5.PaddedTrace

open Rho5

/-- 补零到长度 `n`：不足部分补 `0`。 -/
def padList (n : ℕ) (values : List ℝ) : List ℝ :=
  values ++ List.replicate (n - values.length) 0

/-- 补零的逐步展开：`a :: t` 的补零是 `a` 后接 `t` 的补零（阶数减一）。 -/
theorem padList_cons (n : ℕ) (a : ℝ) (t : List ℝ) :
    padList (n + 1) (a :: t) = a :: padList n t := by
  unfold padList
  rw [List.cons_append, List.length_cons, Nat.succ_sub_succ]

/-- 空列表补零到 `n` 就是 `replicate n 0`。 -/
theorem padList_nil (n : ℕ) : padList n [] = List.replicate n 0 := by
  simp [padList]

/-- 补零后长度恰为 `n`（用原路径长度 ≤ 阶数）。 -/
theorem padList_length {n : ℕ} {values : List ℝ} (h : values.length ≤ n) :
    (padList n values).length = n := by
  unfold padList
  rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' h]

/-- **卡目标 3（原路径 → 补零）**：每条真实合法轨迹的补零都是一条补零轨迹。 -/
theorem padded_of_legalTrace : ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {values : List ℝ},
    Rho5.CompletePivotPath.LegalTrace A values → PaddedLegalTrace A (padList n values)
  | _, _, _, .empty => by
      -- `0 × 0`：原构造器 `empty` 的值是 `[]`
      simpa [padList] using PaddedLegalTrace.empty
  | _, _, _, .zeroStop hzero => by
      -- 正阶零矩阵：原构造器 `zeroStop` 的值是 `[0]`；补零后是零矩阵的 `replicate` 轨迹
      subst hzero
      show PaddedLegalTrace (0 : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ)
        (padList (_ + 1) (0 :: []))
      rw [padList_cons, padList_nil]
      simpa [List.replicate_succ] using padded_zero_replicate (_ + 1)
  | _, _, _, .step p q hmax hne htail => by
      rw [padList_cons]
      exact PaddedLegalTrace.step p q hmax (padded_of_legalTrace htail)

/-- **卡目标 3（补零 → 原路径）**：每条补零轨迹都是某条真实合法轨迹的补零。 -/
theorem exists_legalTrace_of_padded : ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {padded : List ℝ},
    PaddedLegalTrace A padded →
      ∃ values : List ℝ, Rho5.CompletePivotPath.LegalTrace A values ∧ padded = padList n values
  | _, _, _, .empty => ⟨[], Rho5.CompletePivotPath.LegalTrace.empty, by simp [padList]⟩
  | _, A, _, .step p q hmax htail => by
      obtain ⟨values, hvalues, hpad⟩ := exists_legalTrace_of_padded htail
      by_cases hpq : A p q = 0
      · -- 零主元且合法 ⇒ A = 0：原路径走 `zeroStop`，其补零正好是 `|0| :: replicate n 0`
        have hA0 : A = 0 :=
          Rho5.PivotReindex.eq_zero_of_isCompletePivot_of_pivot_eq_zero A p q hmax hpq
        subst hA0
        rw [pivotSchur_zero p q] at htail
        -- the implicit tail of the `.step` pattern is not nameable in this toolchain;
        -- the equation can still be used without naming it
        have hrep := padded_zero_eq_replicate htail
        refine ⟨[0], Rho5.CompletePivotPath.LegalTrace.zeroStop rfl, ?_⟩
        rw [hrep]
        show |(0 : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ) p q| :: List.replicate _ 0
          = padList (_ + 1) (0 :: [])
        rw [padList_cons, padList_nil]
        simp
      · -- 真正的一步：直接用原 `step` 构造器
        refine ⟨|A p q| :: values,
          Rho5.CompletePivotPath.LegalTrace.step p q hmax hpq hvalues, ?_⟩
        rw [hpad, padList_cons]

/-- **卡目标 3（固定双向桥）**：补零轨迹与原合法轨迹的精确对应。 -/
theorem paddedLegalTrace_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (padded : List ℝ) :
    PaddedLegalTrace A padded ↔
      ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ padded = padList n values :=
  ⟨exists_legalTrace_of_padded, fun ⟨values, hvalues, hpad⟩ => by
    rw [hpad]
    exact padded_of_legalTrace hvalues⟩

/-- 原路径的存在性与补零路径的存在性等价。 -/
theorem exists_padded_iff_exists_legalTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ padded : List ℝ, PaddedLegalTrace A padded) ↔
      ∃ values : List ℝ, Rho5.CompletePivotPath.LegalTrace A values :=
  ⟨fun ⟨padded, hp⟩ => by
      obtain ⟨values, hvalues, _⟩ := exists_legalTrace_of_padded hp
      exact ⟨values, hvalues⟩,
    fun ⟨values, hvalues⟩ => ⟨padList n values, padded_of_legalTrace hvalues⟩⟩

end Rho5.PaddedTrace
