/-
D48 — 记号与端点接口：δ、末位 1×1 迹
======================================

本文件只做两件事，避免把记号散进各目标模块：

* 定义卡上要求的 `δ = d - t * s / r`（`d = T2 A 1 1`），并证明它就是真实 D10
  `pivotSchur` 在二阶尾块 `(0,0)` 的唯一条目（接 D46 的 `delta_eq_pivotSchur_zero_zero`）；
* 给出末位 `1 × 1` 块的**统一**读数 `LeadingTracePos B values → values = [|B 0 0|]`，
  它同时覆盖 `lastStep`、`step`（此时尾部必须是 0 阶空迹）与 `zeroStop`（`B = 0`，
  故 `|B 0 0| = 0`）三个分支——**不**假设末位主元非零。

状态模型全部用 D37 已验收的同名 Schur 定义（`S4`/`S3`/`T2`/`p`/`k`/`r`/`s`/`t`），
本卡不重建平行模型；`δ` 是卡上固定记号，不是新的尾块模型。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Certificate.B24Extraction.Extract
import Rho5.Shared.HighGrowthTail
import Rho5.Shared.TailEnvelope
import Rho5.Shared.LeadingSigns

namespace Rho5.CanonicalTail

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **卡上记号 `δ`**：二阶真实尾块 `T2 A = [[r, s], [t, d]]` 在 `(0,0)` 消元后的唯一条目，
`d = T2 A 1 1`、`δ = d - t * s / r`。这是恒等记号（分母 `r` 允许为 `0`，实数除法全定义），
不引入任何非零前提。 -/
noncomputable def delta (A : Matrix5) : ℝ := T2 A 1 1 - t A * s A / r A

/-- **`δ` 的真实 Schur 身份**：`δ A` 恰是真实 D10 `pivotSchur` 在 `T2 A` 的 `(0,0)` 条目
（D46 的冻结等式），因此它就是末位 `1 × 1` 块的主元。 -/
theorem delta_eq_pivotSchur (A : Matrix5) :
    delta A = Rho5.PivotReindex.pivotSchur (T2 A) 0 0 0 0 := by
  rw [delta, Rho5.TailEnvelope.delta_eq_pivotSchur_zero_zero (T2 A)]
  rfl

/-- **`0 × 0` 空迹**：`0 × 0` 矩阵的正性前缀迹只能是空列表（其余构造子的阶数不匹配）。 -/
theorem leadingTracePos_fin_zero {A : Matrix (Fin 0) (Fin 0) ℝ} {values : List ℝ}
    (h : Rho5.LeadingSigns.LeadingTracePos A values) : values = [] := by
  cases h with
  | empty => rfl

/-- **末位 `1 × 1` 统一读数**：`1 × 1` 矩阵的任意正性前缀迹恰有一个值，且就是 `|B 0 0|`。

`lastStep` 直接给出 `[|B 0 0|]`；`step`（阶数 0）的尾部必须是 `0 × 0` 的空迹；
`zeroStop` 要求 `B = 0`，于是 `|B 0 0| = 0` 与 `[0]` 一致。三个分支都覆盖，
**不**假设末位主元非零。 -/
theorem leadingTracePos_fin_one {B : Matrix (Fin 1) (Fin 1) ℝ} {values : List ℝ}
    (h : Rho5.LeadingSigns.LeadingTracePos B values) : values = [|B 0 0|] := by
  have hhead : values.head? = some |B 0 0| := by
    cases h with
    | zeroStop hzero => rw [hzero]; simp
    | lastStep hmax hne => simp
    | step hmax hne hpos htail => simp [abs_of_pos hpos]
  have hlen : values.length ≤ 1 := by
    have hl : Rho5.CompletePivotPath.LegalTrace B values :=
      Rho5.LeadingTrace.legalTrace_of_leading
        (Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos h)
    simpa using Rho5.CompletePivotPath.length_le hl
  cases values with
  | nil => simp at hhead
  | cons a t =>
      cases t with
      | nil =>
          have ha : a = |B 0 0| := by simpa using hhead
          simp [ha]
      | cons b t' => simp at hlen

/-- **末位 zeroStop 覆盖**：末位 `1 × 1` 块为零时其正性前缀迹是 `[0]`，而 `|B 0 0| = 0`；
这条显式记录「最后值允许为 0」，所以 `values.length = 5` 不能被读成满秩或末主元非零。 -/
theorem leadingTracePos_fin_one_zeroStop {B : Matrix (Fin 1) (Fin 1) ℝ} (hB : B = 0) :
    Rho5.LeadingSigns.LeadingTracePos B [0] ∧ (|B 0 0| : ℝ) = 0 :=
  ⟨Rho5.LeadingSigns.LeadingTracePos.zeroStop hB, by rw [hB]; simp⟩

end Rho5.CanonicalTail
