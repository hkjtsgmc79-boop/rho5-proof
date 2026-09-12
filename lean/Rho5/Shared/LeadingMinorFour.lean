/-
D49 — 五阶前四个首位置主元限制到真实四阶主子矩阵
=================================================

把全局高增长第四步分支变成**真正四阶完全主元消元**的实例，供将来四阶尖锐上界消费。
本卡**不**证明任何四阶尖锐上界。

固定 `M : Matrix5`。唯一局部辅助是左上 4×4 主子矩阵

`A4 M := fun i j => M i.castSucc j.castSucc`

固定 `(0,0)` 顺序，证明限制与前三次真实 Schur 消元相容。元素公式走原 D10
`PivotReindex.pivotSchur_apply` + `PivotReindex.remainingIndex`（经 D40
`remainingIndex_zero` 读成 `succ`），只做 5→4、4→3、3→2 三层，**不**建立任意嵌入 /
任意子矩阵框架。记 D37 冻结坐标

`S4 M = pivotSchur M 0 0`（4×4）、`S3 M = pivotSchur (S4 M) 0 0`（3×3）、
`T2 M = pivotSchur (S3 M) 0 0`（2×2）、`p M = S4 M 0 0`、`k M = S3 M 0 0`、
`r M = T2 M 0 0`。

在卡列出的实际前提（`M 0 0 = 1`；`M`/`S4 M`/`S3 M`/`T2 M` 在 `(0,0)` 的真实 CP；
`p M > 0`、`k M > 0`、`r M > 0`）下：

* `A4 M` 有真实原 D13 迹 `[1, p M, k M, r M]`；四个阶段的主元性**全部由全矩阵 CP 链限制得到**
  （`M → A4`、`S4 M → pivotSchur A4`、`S3 M → pivotSchur² A4`、`T2 M → pivotSchur³ A4`），
  没有把受限块的 CP 额外假设；最后四阶 `1 × 1` 由 `r M > 0` 付清（它的 CP 同样来自 `T2 M`）；
* 前三个真实 Schur 角主元逐项对应原 5 阶链前四值（`corner_values_eq`）；
* `matrixEntryMax M = 1` 时 `stageEntryMax (A4 M) = 1`（用 D12 的**实际 4×4**
  `MatrixStage.stageEntryMax`，不是 `Matrix5` 的固定归一化定义）、`A4 M ≠ 0`，
  四阶路径峰值 = `max` 链 `≥ r M`；
* 给出真实四阶矩阵/路径见证 `exists_A4_witness`，供未来四阶上界定理接入。

**不声明**：不证明四阶尖锐上界，不宣称 `r ≤ 4`、`rho5 ≤ 4` 或任何全域 alpha 上界；不建立
任意维嵌入或任意子矩阵框架；不重审上游、不重复已冻结依赖的审核。

只读复用（冻结输入）：D08 `MatrixNormalization`、D10 `PivotReindex`、D12 `MatrixStage`、
D13 `CompletePivotPath`、D17 `GrowthModel`、D40 `LeadingTrace`、D37
`Certificate.B24Extraction.Extract`（`S4`/`S3`/`T2`/`p`/`k`/`r` 及其 `_apply` 公式）。
无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Rho5.Shared.Conventions
import Rho5.Shared.Pivot
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.MatrixStage
import Rho5.Shared.PivotReindex
import Rho5.Shared.CompletePivotPath
import Rho5.Shared.GrowthModel
import Rho5.Shared.LeadingTrace
import Rho5.Certificate.B24Extraction.Extract

namespace Rho5.LeadingMinorFour

open Rho5
open Rho5.Certificate.B24Extraction

/-! ## 0. 唯一局部辅助：左上 4×4 主子矩阵 -/

/-- **唯一局部辅助（卡固定）**：`M` 的左上 4×4 主子矩阵 `A4 M i j = M i.castSucc j.castSucc`。
不定义任何别的矩阵/嵌入：其余限制都写成 `A4` 上逐次真实 `pivotSchur` 与 D37 冻结坐标的比对。 -/
def A4 (M : Matrix5) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => M i.castSucc j.castSucc

/-- `A4` 的角条目就是 `M 0 0`。 -/
theorem A4_zero_zero (M : Matrix5) : A4 M 0 0 = M 0 0 := rfl

/-- **目标 6（非零）**：`M 0 0 = 1` 时 `A4 M ≠ 0`（角条目非零即矩阵非零）。 -/
theorem A4_ne_zero (M : Matrix5) (h00 : M 0 0 = 1) : A4 M ≠ 0 := by
  intro h
  have h' : A4 M 0 0 = 0 := by rw [h]; rfl
  rw [A4_zero_zero, h00] at h'
  exact one_ne_zero h'

/-! ## 1. 限制与前三次首位置 Schur 消元相容（5→4、4→3、3→2） -/

/-- **层 5→4（元素公式）**：`A4 M` 上的一次真实 D10 首位置消元，逐条目等于
`S4 M = pivotSchur M 0 0` 的左上 3×3（下标经 `Fin.castSucc` 嵌入）。
用原 D10 `pivotSchur_apply` + 原 `remainingIndex`（经 D40 `remainingIndex_zero`），
只做这一固定层，不引入子矩阵框架。 -/
theorem pivotSchur_A4_apply (M : Matrix5) (i j : Fin 3) :
    PivotReindex.pivotSchur (A4 M) 0 0 i j = S4 M i.castSucc j.castSucc := by
  rw [PivotReindex.pivotSchur_apply]
  simp only [LeadingTrace.remainingIndex_zero]
  rw [S4_apply]
  simp only [A4, Fin.castSucc_succ, Fin.castSucc_zero]

/-- **层 4→3（元素公式）**：再消一次，逐条目等于 `S3 M = pivotSchur (S4 M) 0 0` 的左上 2×2。 -/
theorem pivotSchur₂_A4_apply (M : Matrix5) (i j : Fin 2) :
    PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 i j
      = S3 M i.castSucc j.castSucc := by
  rw [PivotReindex.pivotSchur_apply]
  simp only [LeadingTrace.remainingIndex_zero]
  rw [S3_apply]
  rw [pivotSchur_A4_apply M i.succ j.succ, pivotSchur_A4_apply M i.succ 0,
    pivotSchur_A4_apply M 0 j.succ, pivotSchur_A4_apply M 0 0]
  simp only [Fin.castSucc_succ, Fin.castSucc_zero]

/-- **层 3→2（元素公式）**：第三次消元后逐条目等于 `T2 M = pivotSchur (S3 M) 0 0`
的左上 1×1；这就是四次真实角主元里的第四个值 `r M` 所在层。 -/
theorem pivotSchur₃_A4_apply (M : Matrix5) (i j : Fin 1) :
    PivotReindex.pivotSchur
        (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 i j
      = T2 M i.castSucc j.castSucc := by
  rw [PivotReindex.pivotSchur_apply]
  simp only [LeadingTrace.remainingIndex_zero]
  rw [T2_apply]
  rw [pivotSchur₂_A4_apply M i.succ j.succ, pivotSchur₂_A4_apply M i.succ 0,
    pivotSchur₂_A4_apply M 0 j.succ, pivotSchur₂_A4_apply M 0 0]
  simp only [Fin.castSucc_succ, Fin.castSucc_zero]

/-- **角主元 1（`p M`）**：限制链第一层消元后的角条目就是 D37 的 `p M = S4 M 0 0`。 -/
theorem pivotSchur_A4_zero_zero (M : Matrix5) :
    PivotReindex.pivotSchur (A4 M) 0 0 0 0 = p M := by
  rw [pivotSchur_A4_apply M 0 0]
  rfl

/-- **角主元 2（`k M`）**：限制链第二层消元后的角条目就是 D37 的 `k M = S3 M 0 0`。 -/
theorem pivotSchur₂_A4_zero_zero (M : Matrix5) :
    PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0 = k M := by
  rw [pivotSchur₂_A4_apply M 0 0]
  rfl

/-- **角主元 3（`r M`）**：限制链第三层消元后的角条目就是 D37 的 `r M = T2 M 0 0`。 -/
theorem pivotSchur₃_A4_zero_zero (M : Matrix5) :
    PivotReindex.pivotSchur
        (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0 = r M := by
  rw [pivotSchur₃_A4_apply M 0 0]
  rfl

/-! ## 2. 完整主元由全矩阵条目界限制得到（不是额外假设） -/

/-- **CP 限制（层 5→4）**：`M` 在 `(0,0)` 的完整主元直接限制到 `A4 M`：条目的绝对值界是
同一个 `|M 0 0|`，只需取出 `i.castSucc`、`j.castSucc` 两条实例。 -/
theorem isCompletePivot_A4 (M : Matrix5) (h : Pivot.IsCompletePivot M 0 0) :
    Pivot.IsCompletePivot (A4 M) 0 0 := by
  intro i j
  simpa only [A4] using h i.castSucc j.castSucc

/-- **CP 限制（层 4→3）**：`S4 M` 的 `(0,0)` 完整主元经层 5→4 元素公式限制到
`pivotSchur (A4 M) 0 0`。 -/
theorem isCompletePivot_pivotSchur_A4 (M : Matrix5)
    (h : Pivot.IsCompletePivot (S4 M) 0 0) :
    Pivot.IsCompletePivot (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 := by
  intro i j
  rw [pivotSchur_A4_apply M i j, pivotSchur_A4_zero_zero M]
  simpa only [p] using h i.castSucc j.castSucc

/-- **CP 限制（层 3→2）**：`S3 M` 的 `(0,0)` 完整主元经层 4→3 元素公式限制到
`pivotSchur² (A4 M)`。 -/
theorem isCompletePivot_pivotSchur₂_A4 (M : Matrix5)
    (h : Pivot.IsCompletePivot (S3 M) 0 0) :
    Pivot.IsCompletePivot (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 := by
  intro i j
  rw [pivotSchur₂_A4_apply M i j, pivotSchur₂_A4_zero_zero M]
  simpa only [k] using h i.castSucc j.castSucc

/-- **CP 限制（层 2→1）**：`T2 M` 的 `(0,0)` 完整主元经层 3→2 元素公式限制到
`pivotSchur³ (A4 M)`；这就是最后 4 阶 `1 × 1` 阶段的主元性，卡上列的 `T2 M` CP 前提在此被消费。 -/
theorem isCompletePivot_pivotSchur₃_A4 (M : Matrix5)
    (h : Pivot.IsCompletePivot (T2 M) 0 0) :
    Pivot.IsCompletePivot
      (PivotReindex.pivotSchur
        (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0) 0 0 := by
  intro i j
  rw [pivotSchur₃_A4_apply M i j, pivotSchur₃_A4_zero_zero M]
  simpa only [r] using h i.castSucc j.castSucc

/-! ## 3. 真实四阶原 D13 迹 `[1, p M, k M, r M]` -/

/-- **卡主目标（真实原 D13 迹）**：在卡列出的全部实际前提下，左上 4×4 主子矩阵 `A4 M` 携带
真实 `Rho5.CompletePivotPath.LegalTrace`，值表 `[1, p M, k M, r M]`。

四个阶段逐项对应：角 `1 = M 0 0`（前提），`p M`（`S4 M` 的角），`k M`（`S3 M` 的角），
`r M`（`T2 M` 的角，即最后 `1 × 1` 阶段，由 `r M > 0` 付清非零）。每一步的完整主元都由
§2 的限制引理从全矩阵 CP 链**推出**，没有任何受限块的 CP 是假设。 -/
theorem legalTrace_A4 (M : Matrix5) (h00 : M 0 0 = 1)
    (hM : Pivot.IsCompletePivot M 0 0) (hS4 : Pivot.IsCompletePivot (S4 M) 0 0)
    (hS3 : Pivot.IsCompletePivot (S3 M) 0 0) (hT2 : Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    CompletePivotPath.LegalTrace (A4 M) [1, p M, k M, r M] := by
  have hval1 : |A4 M 0 0| = 1 := by rw [A4_zero_zero, h00, abs_one]
  have hval2 : |PivotReindex.pivotSchur (A4 M) 0 0 0 0| = p M := by
    rw [pivotSchur_A4_zero_zero, abs_of_pos hp]
  have hval3 : |PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0| = k M := by
    rw [pivotSchur₂_A4_zero_zero, abs_of_pos hk]
  have hval4 : |PivotReindex.pivotSchur
      (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0| = r M := by
    rw [pivotSchur₃_A4_zero_zero, abs_of_pos hr]
  have htrace : CompletePivotPath.LegalTrace (A4 M)
      [|A4 M 0 0|, |PivotReindex.pivotSchur (A4 M) 0 0 0 0|,
        |PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0|,
        |PivotReindex.pivotSchur
          (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0|] := by
    refine CompletePivotPath.LegalTrace.step (0 : Fin 4) 0 (isCompletePivot_A4 M hM) ?_ ?_
    · rw [A4_zero_zero, h00]; exact one_ne_zero
    · refine CompletePivotPath.LegalTrace.step (0 : Fin 3) 0
        (isCompletePivot_pivotSchur_A4 M hS4) ?_ ?_
      · rw [pivotSchur_A4_zero_zero]; exact ne_of_gt hp
      · refine CompletePivotPath.LegalTrace.step (0 : Fin 2) 0
          (isCompletePivot_pivotSchur₂_A4 M hS3) ?_ ?_
        · rw [pivotSchur₂_A4_zero_zero]; exact ne_of_gt hk
        · refine CompletePivotPath.LegalTrace.step (0 : Fin 1) 0
            (isCompletePivot_pivotSchur₃_A4 M hT2) ?_ ?_
          · rw [pivotSchur₃_A4_zero_zero]; exact ne_of_gt hr
          · have hz : PivotReindex.pivotSchur
                (PivotReindex.pivotSchur
                  (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0) 0 0 = 0 := by
              funext i j
              exact Fin.elim0 i
            rw [hz]
            exact CompletePivotPath.LegalTrace.empty
  simpa only [hval1, hval2, hval3, hval4] using htrace

/-- **卡目标（前三次角主元逐项对应 5 阶前四值）**：四个真实角值合起来正是原 5 阶链前四值
`[1, p M, k M, r M]`：第一项是 `A4 M 0 0 = M 0 0 = 1`，后三项分别是 `S4 M`、`S3 M`、`T2 M`
的角条目（由 §1 的层引理逐项对应）。 -/
theorem corner_values_eq (M : Matrix5) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    [|A4 M 0 0|, |PivotReindex.pivotSchur (A4 M) 0 0 0 0|,
      |PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0|,
      |PivotReindex.pivotSchur
        (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0|]
      = [1, p M, k M, r M] := by
  simp only [A4_zero_zero, h00, abs_one, pivotSchur_A4_zero_zero, abs_of_pos hp,
    pivotSchur₂_A4_zero_zero, abs_of_pos hk, pivotSchur₃_A4_zero_zero, abs_of_pos hr]

/-- **卡目标（可选 D40 首位置口径）**：同一条真实路径写成 D40 的 `LeadingLegalTrace`
（主元固定在 `(0,0)`，仍要求真实 CP + 非零主元）；前提与 `legalTrace_A4` 完全一致。 -/
theorem leadingLegalTrace_A4 (M : Matrix5) (h00 : M 0 0 = 1)
    (hM : Pivot.IsCompletePivot M 0 0) (hS4 : Pivot.IsCompletePivot (S4 M) 0 0)
    (hS3 : Pivot.IsCompletePivot (S3 M) 0 0) (hT2 : Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    LeadingTrace.LeadingLegalTrace (A4 M) [1, p M, k M, r M] := by
  have hval1 : |A4 M 0 0| = 1 := by rw [A4_zero_zero, h00, abs_one]
  have hval2 : |PivotReindex.pivotSchur (A4 M) 0 0 0 0| = p M := by
    rw [pivotSchur_A4_zero_zero, abs_of_pos hp]
  have hval3 : |PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0| = k M := by
    rw [pivotSchur₂_A4_zero_zero, abs_of_pos hk]
  have hval4 : |PivotReindex.pivotSchur
      (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0| = r M := by
    rw [pivotSchur₃_A4_zero_zero, abs_of_pos hr]
  have htrace : LeadingTrace.LeadingLegalTrace (A4 M)
      [|A4 M 0 0|, |PivotReindex.pivotSchur (A4 M) 0 0 0 0|,
        |PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0 0 0|,
        |PivotReindex.pivotSchur
          (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0 0 0|] := by
    refine LeadingTrace.LeadingLegalTrace.step (isCompletePivot_A4 M hM) ?_ ?_
    · rw [A4_zero_zero, h00]; exact one_ne_zero
    · refine LeadingTrace.LeadingLegalTrace.step (isCompletePivot_pivotSchur_A4 M hS4) ?_ ?_
      · rw [pivotSchur_A4_zero_zero]; exact ne_of_gt hp
      · refine LeadingTrace.LeadingLegalTrace.step (isCompletePivot_pivotSchur₂_A4 M hS3) ?_ ?_
        · rw [pivotSchur₂_A4_zero_zero]; exact ne_of_gt hk
        · refine LeadingTrace.LeadingLegalTrace.step (isCompletePivot_pivotSchur₃_A4 M hT2) ?_ ?_
          · rw [pivotSchur₃_A4_zero_zero]; exact ne_of_gt hr
          · have hz : PivotReindex.pivotSchur
                (PivotReindex.pivotSchur
                  (PivotReindex.pivotSchur (PivotReindex.pivotSchur (A4 M) 0 0) 0 0) 0 0) 0 0 = 0 := by
              funext i j
              exact Fin.elim0 i
            rw [hz]
            exact LeadingTrace.LeadingLegalTrace.empty
  simpa only [hval1, hval2, hval3, hval4] using htrace

/-! ## 4. 归一化与峰值资格（目标 6） -/

/-- **目标 6（限制不增条目）**：`A4 M` 的每个条目绝对值 ≤ `matrixEntryMax M`。 -/
theorem abs_entry_le_matrixEntryMax_A4 (M : Matrix5) (i j : Fin 4) :
    |A4 M i j| ≤ matrixEntryMax M := by
  simpa only [A4] using MatrixNormalization.abs_entry_le_matrixEntryMax M i.castSucc j.castSucc

/-- **目标 6（四阶 `stageEntryMax` 归一化）**：`matrixEntryMax M = 1` 且 `M 0 0 = 1` 时，
真实四阶 `MatrixStage.stageEntryMax (A4 M) = 1`。

两侧都实打实：`≤` 由最大条目被某条目达到 + 限制不增条目得到，`≥` 由角条目 `|A4 M 0 0| = 1`
得到。这里用的是 D12 的**实际 4×4** `stageEntryMax`，没有偷用 `Matrix5` 的固定归一化定义。 -/
theorem stageEntryMax_A4_eq_one (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1) :
    MatrixStage.stageEntryMax (A4 M) = 1 := by
  obtain ⟨i, j, hij⟩ := MatrixStage.exists_abs_entry_eq_stageEntryMax (A4 M)
  have hle : MatrixStage.stageEntryMax (A4 M) ≤ 1 := by
    rw [← hij, ← hmax]
    exact abs_entry_le_matrixEntryMax_A4 M i j
  have hge : 1 ≤ MatrixStage.stageEntryMax (A4 M) := by
    have h := MatrixStage.abs_entry_le_stageEntryMax (A4 M) 0 0
    rwa [A4_zero_zero, h00, abs_one] at h
  exact le_antisymm hle hge

/-- **目标 6（四阶段峰值 = `max` 链）**：四项全非负的第四项（真实轨迹末项是 `r M > 0`）时，
`tracePeak` 就是四项 `max` 链；不引入任何新峰值定义。 -/
theorem tracePeak_four {a b c d : ℝ} (hd : 0 ≤ d) :
    GrowthModel.tracePeak [a, b, c, d] = max a (max b (max c d)) := by
  rw [GrowthModel.tracePeak_cons, GrowthModel.tracePeak_cons, GrowthModel.tracePeak_cons,
    GrowthModel.tracePeak_cons, GrowthModel.tracePeak_nil, max_eq_left hd]

/-- **目标 6（四阶路径峰值 = `max` 链 ≥ `r M`）**：真实四阶段值 `[1, p M, k M, r M]` 的
`tracePeak` 等于 `max 1 (max (p M) (max (k M) (r M)))`，且该峰值 ≥ `r M`。 -/
theorem tracePeak_A4_values (M : Matrix5) (hr : 0 < r M) :
    GrowthModel.tracePeak [1, p M, k M, r M] = max 1 (max (p M) (max (k M) (r M))) ∧
      r M ≤ GrowthModel.tracePeak [1, p M, k M, r M] := by
  have hpeak : GrowthModel.tracePeak [1, p M, k M, r M]
      = max 1 (max (p M) (max (k M) (r M))) :=
    tracePeak_four (a := (1 : ℝ)) (b := p M) (c := k M) (d := r M) (le_of_lt hr)
  refine ⟨hpeak, ?_⟩
  rw [hpeak]
  exact (le_max_right (k M) (r M)).trans
    ((le_max_right (p M) (max (k M) (r M))).trans
      (le_max_right (1 : ℝ) (max (p M) (max (k M) (r M)))))

/-- **卡目标（真实四阶矩阵/路径见证接口）**：在卡的完整前提加 `matrixEntryMax M = 1` 下，
存在真实四阶矩阵 `B = A4 M`：非零、`stageEntryMax B = 1`、携带原 D13 合法迹
`[1, p M, k M, r M]`，且该路径峰值等于 `max` 链并 `≥ r M`。

这是给未来四阶尖锐上界定理接入的接口：上界本身**不在本卡**。 -/
theorem exists_A4_witness (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hM : Pivot.IsCompletePivot M 0 0) (hS4 : Pivot.IsCompletePivot (S4 M) 0 0)
    (hS3 : Pivot.IsCompletePivot (S3 M) 0 0) (hT2 : Pivot.IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    ∃ B : Matrix (Fin 4) (Fin 4) ℝ,
      B = A4 M ∧ B ≠ 0 ∧ MatrixStage.stageEntryMax B = 1 ∧
        CompletePivotPath.LegalTrace B [1, p M, k M, r M] ∧
          GrowthModel.tracePeak [1, p M, k M, r M]
              = max 1 (max (p M) (max (k M) (r M))) ∧
            r M ≤ GrowthModel.tracePeak [1, p M, k M, r M] :=
  ⟨A4 M, rfl, A4_ne_zero M h00, stageEntryMax_A4_eq_one M hmax h00,
    legalTrace_A4 M h00 hM hS4 hS3 hT2 hp hk hr,
    (tracePeak_A4_values M hr).1, (tracePeak_A4_values M hr).2⟩

end Rho5.LeadingMinorFour
