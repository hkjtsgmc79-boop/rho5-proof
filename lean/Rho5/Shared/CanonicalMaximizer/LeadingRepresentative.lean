/-
D43 — 阶段 A（2）：归一化首位置路径的真实全局极大见证
======================================================

在阶段 A（1）（`GlobalMax`）之上，把 D38 阶段 C 的**实际首主元域峰值见证**经 D40 的
**静态行列置换**变成条目最大值 `1`、带**首位置** `LeadingLegalTrace` 的真实 `Matrix5`，
并保留同一个全局比较。

* 取自 D38：`exists_tracePeak_eq_rho5Trace` 给出 `A ∈ firstPivotDomain`（因此
  `matrixEntryMax A = 1`）与真实 `LegalTrace A values`、`tracePeak values = rho5Trace`；
* 取自 D40：`exists_leading_normalized_growth_witness` 给出**一次静态重排**
  `B = permuteEntries A ρ κ`，满足 `matrixEntryMax B = 1` 且 `LeadingLegalTrace B values`
  ——值列表逐项保持（首个值就是 `|B 0 0|`），早停与并列语义不变；
* `growthRatio B values = rho5Trace` 由 D17 的
  `growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one`（归一化后比值即峰值）得到；
* 全局比较与 A（1）逐字相同，由 `growthRatio_le_rho5Trace` 在等式上改写得到。

**明确不宣称**：`B 0 0 = 1`（首位置主元只知非零；符号规范化是 D41 的范围，D41 未交付前
不得把 `±1` 的情形直接当成 `+1`）、五个主元非零、满秩、尾块平衡、`rho5Trace = alpha`。
值列表**不**被补长成 5 项：它仍来自 D38 的真实见证，长度只满足 `values.length ≤ 5`
（D13 `length_le_five` 经 D40 的单向桥）。

只读复用（不重编）：D38 `Rho5.Shared.TraceAttainment`、D40 `Rho5.Shared.LeadingTrace`、
D13 `Rho5.Shared.CompletePivotPath`、D17 `Rho5.Shared.GrowthModel`、D20
`Rho5.Shared.TracePermutation`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.CanonicalMaximizer.GlobalMax
import Rho5.Shared.LeadingTrace

namespace Rho5.CanonicalMaximizer

open Rho5

/-- **A2（带置换来源的归一化首位置极大见证）**：存在 D38 的实际首主元域见证 `A`、一次静态
行列置换 `ρ κ`、重排后的 `B = permuteEntries A ρ κ` 与真实值列表 `values`，使
`matrixEntryMax B = 1`、`B ≠ 0`、`LeadingLegalTrace B values`、
`growthRatio B values = rho5Trace`，且对每个真实非零矩阵与每条原 `LegalTrace` 给出上界。 -/
theorem exists_leading_normalized_maximizer :
    ∃ (A B : Matrix5) (ρ κ : Equiv.Perm (Fin 5)) (values : List ℝ),
      A ∈ Rho5.FirstPivotCompact.firstPivotDomain ∧
        B = Rho5.TracePermutation.permuteEntries A ρ κ ∧
          matrixEntryMax B = 1 ∧ B ≠ 0 ∧
            Rho5.LeadingTrace.LeadingLegalTrace B values ∧
              Rho5.GrowthModel.growthRatio B values = Rho5.GrowthSupremum.rho5Trace ∧
                ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
                  Rho5.CompletePivotPath.LegalTrace N ws →
                    Rho5.GrowthModel.growthRatio N ws ≤
                      Rho5.GrowthModel.growthRatio B values := by
  obtain ⟨A, hA, values, htrace, hpeak⟩ := Rho5.TraceAttainment.exists_tracePeak_eq_rho5Trace
  obtain ⟨hmaxA, hA00, hApiv⟩ := hA
  have hAne : A ≠ 0 := Rho5.GrowthModel.ne_zero_of_matrixEntryMax_eq_one hmaxA
  obtain ⟨B, ρ, κ, hB, hmaxB, -, hleading⟩ :=
    Rho5.LeadingTrace.exists_leading_normalized_growth_witness (A := A) (values := values)
      (g := Rho5.GrowthModel.tracePeak values) hmaxA htrace rfl
  have hBne : B ≠ 0 := by
    rw [hB]
    exact (Rho5.TracePermutation.permuteEntries_ne_zero_iff A ρ κ).mpr hAne
  have hratio : Rho5.GrowthModel.growthRatio B values = Rho5.GrowthSupremum.rho5Trace := by
    rw [Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmaxB, hpeak]
  exact ⟨A, B, ρ, κ, values, ⟨hmaxA, hA00, hApiv⟩, hB, hmaxB, hBne, hleading, hratio,
    fun N hN ws hws => by
    rw [hratio]
    exact growthRatio_le_rho5Trace hN hws⟩

/-- **A2（下游直接消费形式）**：只需矩阵本身——条目最大值 `1`、非零、带首位置
`LeadingLegalTrace`、增长比等于 `rho5Trace`，并对所有真实矩阵/路径给出上界。 -/
theorem exists_normalized_leading_maximizer :
    ∃ M : Matrix5, matrixEntryMax M = 1 ∧ M ≠ 0 ∧ ∃ values : List ℝ,
      Rho5.LeadingTrace.LeadingLegalTrace M values ∧
        Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
          ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
            Rho5.CompletePivotPath.LegalTrace N ws →
              Rho5.GrowthModel.growthRatio N ws ≤ Rho5.GrowthModel.growthRatio M values := by
  obtain ⟨-, B, -, -, values, -, -, hmaxB, hBne, hleading, hratio, hcmp⟩ :=
    exists_leading_normalized_maximizer
  exact ⟨B, hmaxB, hBne, values, hleading, hratio, hcmp⟩

/-- **A2（首位置主元非零，但不等于 `+1`）**：任何非零矩阵的首位置 `LeadingLegalTrace`
都从真实 `step` 开始，故 `B 0 0 ≠ 0`；`zeroStop` 分支要求矩阵为零，与非零性矛盾。这里
**不**断言 `B 0 0 = 1`——首位置重排只保证条目最大值归一，符号由 D41 处理。 -/
theorem leading_corner_ne_zero {B : Matrix5} {values : List ℝ}
    (h : Rho5.LeadingTrace.LeadingLegalTrace B values) (hB : B ≠ 0) : B 0 0 ≠ 0 := by
  cases h with
  | zeroStop hzero => exact absurd hzero hB
  | step hmax hne htail => exact hne

/-- **A2（值列表首项 = 首位置主元的绝对值）**：非零矩阵的首位置路径必然以
`|B 0 0| :: tail` 的形式记录，长度与早停语义原样保留，不补长、不改写。 -/
theorem exists_cons_of_leading {B : Matrix5} {values : List ℝ}
    (h : Rho5.LeadingTrace.LeadingLegalTrace B values) (hB : B ≠ 0) :
    ∃ tail : List ℝ, values = |B 0 0| :: tail := by
  cases h with
  | zeroStop hzero => exact absurd hzero hB
  | step hmax hne htail => exact ⟨_, rfl⟩

/-- **A2（长度语义）**：首位置路径经 D40 的单向桥仍是原 `LegalTrace`，故 D13 的长度上界
`values.length ≤ 5` 成立——本卡**不**假定五步满长。 -/
theorem leading_length_le_five {B : Matrix5} {values : List ℝ}
    (h : Rho5.LeadingTrace.LeadingLegalTrace B values) : values.length ≤ 5 :=
  Rho5.CompletePivotPath.length_le_five (Rho5.LeadingTrace.legalTrace_of_leading h)

/-- **A2（汇总接口）**：一个可直接交给下游分类定理的完整见证——条目最大值 `1`、非零、
首位置主元非零、真实首位置轨迹、长度 `≤ 5`、增长比等于 `rho5Trace`、以及对所有真实
矩阵/路径的全局上界。所有合取项都是结论；没有任何一项是前提或证书假设。 -/
theorem exists_leading_normalized_maximizer_full :
    ∃ M : Matrix5, matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 ≠ 0 ∧
      ∃ values : List ℝ,
        Rho5.LeadingTrace.LeadingLegalTrace M values ∧ values.length ≤ 5 ∧
          Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
            ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
              Rho5.CompletePivotPath.LegalTrace N ws →
                Rho5.GrowthModel.growthRatio N ws ≤ Rho5.GrowthModel.growthRatio M values := by
  obtain ⟨M, hmax, hne, values, hleading, hratio, hcmp⟩ := exists_normalized_leading_maximizer
  exact ⟨M, hmax, hne, leading_corner_ne_zero hleading hne, values, hleading,
    leading_length_le_five hleading, hratio, hcmp⟩

end Rho5.CanonicalMaximizer
