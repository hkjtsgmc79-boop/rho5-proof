/-
D43 — 阶段 B：消费已证 D41 符号核心，组装真实五阶规范最大代表
=================================================================

**阶段 B 的门**：D41 的 `results/LEADING_SIGNS_CORE_READY.json` 已发布，且其记录的
`source_sha256 = 6424a945…`、`olean_sha256 = 2b831643…` 与 X 上
`D41/src/Rho5/Shared/LeadingSigns.lean`、`D41/build/lib/…/LeadingSigns.olean` 逐字节一致
（绑定回执见 `results/INPUT_BINDING.json`）。本模块只读消费 D41 **已证核心**
（`LeadingTracePos`、`leadingLegalTrace_of_leadingTracePos`、`exists_signs_leadingTracePos`）
与 D22 已验收的符号不变性（`matrixEntryMax_signedEntries5`、`growthRatio_signedEntries5`、
`signedEntries5_ne_zero_of_ne_zero`），不重复它们的证明，也不引用 D41 未编译的
`GOAL3_ATTEMPT.md`。

**组装路线**（全部从已验具体接口推出，无新假设）：

1. 阶段 A 的 `exists_normalized_leading_maximizer` 给出真实 `A`：`matrixEntryMax A = 1`、
   `A ≠ 0`、`LeadingLegalTrace A values`、`growthRatio A values = rho5Trace`、全局比较；
2. D41 `exists_signs_leadingTracePos` 对该矩阵选出**静态行符号** `s`（`IsSign s`），使
   `LeadingTracePos (signedEntries A s 1) values`——同一值列表，除最后 `1 × 1` 主元外每个
   主元严格为正；最后一行符号保持 `+1`，早停 `zeroStop` 的零主元不声称正；
3. D22 的不变性把归一化与增长搬到符号化矩阵：`matrixEntryMax`（`= 1`）、非零性、
   `growthRatio`（`= rho5Trace`）全部保持；
4. 首位置主元：`LeadingTracePos` 的非零矩阵首步给出 `0 < B 0 0` 与 `IsCompletePivot B 0 0`；
   后者配 `matrixEntryMax B = 1` 得 `|B 0 0| = 1`，于是 `B 0 0 = 1`——**真实首主元 +1**，
   且值列表首项就是正的 `B 0 0`。

**保留**：原值列表（不补长、不改写）、全局比较、`values.length ≤ 5`、峰值等式
`tracePeak values = rho5Trace`。**不声称**：最后 `1 × 1` 主元为正、五个非零主元、满秩、
尾块平衡、`rho5Trace = alpha`、B24 覆盖或任何具体数值矩阵。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.CanonicalMaximizer.LeadingRepresentative
import Rho5.Shared.LeadingSigns
import Rho5.Shared.TraceSigns.GrowthAdapter

namespace Rho5.CanonicalMaximizer

open Rho5

/-! ## 1. 两个端点事实（自证的小工具，供组装使用） -/

/-- **端点事实 1**：`matrixEntryMax` 为 `1` 的完整主元，其绝对值就是 `1`。

上界方向是 D08 的 `abs_entry_le_matrixEntryMax`；下界方向用完整主元的定义
（`∀ i j, |B i j| ≤ |B 0 0|`，即角条目同时是 25 个绝对值的上确界）。 -/
theorem abs_corner_eq_one_of_isCompletePivot {B : Matrix5}
    (hmax : Rho5.Pivot.IsCompletePivot B 0 0) (h : matrixEntryMax B = 1) : |B 0 0| = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← h]
    exact Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax B 0 0
  · rw [← h]
    unfold Rho5.matrixEntryMax
    exact Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => hmax ij.1 ij.2)

/-- **端点事实 2**：非零矩阵的 `LeadingTracePos` 首步是真实 `step`：首位置主元既严格为正，
又是完整主元（`zeroStop` 要求矩阵为零，与 `B ≠ 0` 矛盾；`empty`/`lastStep` 的阶数不匹配）。 -/
theorem leadingTracePos_step_facts {B : Matrix5} {values : List ℝ}
    (h : Rho5.LeadingSigns.LeadingTracePos B values) (hB : B ≠ 0) :
    0 < B 0 0 ∧ Rho5.Pivot.IsCompletePivot B 0 0 := by
  cases h with
  | zeroStop hzero => exact absurd hzero hB
  | step hmax hne hpos htail => exact ⟨hpos, hmax⟩

/-- **端点事实 3**：正性前缀路径的首个记录值就是**正的**首位置主元本身（不是它的绝对值），
值列表因此以 `B 0 0 :: tail` 开头，早停与长度语义原样保留。 -/
theorem exists_cons_of_leadingTracePos {B : Matrix5} {values : List ℝ}
    (h : Rho5.LeadingSigns.LeadingTracePos B values) (hB : B ≠ 0) :
    ∃ tail : List ℝ, values = B 0 0 :: tail := by
  cases h with
  | zeroStop hzero => exact absurd hzero hB
  | step hmax hne hpos htail => exact ⟨_, rfl⟩

/-! ## 2. 阶段 B 主定理：真实五阶规范最大代表 -/

/-- **阶段 B（组装）**：存在真实非零 `Matrix5` `A`（阶段 A 的条目最大值 `1` 首位置最大
矩阵）、静态行符号 `s`（`IsSign s`）与真实值列表 `values`，使 `B = signedEntries A s 1`
满足

* `matrixEntryMax B = 1`、`B ≠ 0`（D22 符号不变性 + 阶段 A）；
* `B 0 0 = 1`：**真实首主元 +1**（D41 正主元资格 + 端点事实 1）；
* `LeadingTracePos B values`：**正前缀**——除最后 `1 × 1` 主元外每个主元严格为正，
  最后一行符号 `+1`，早停零主元不声称正；
* `LeadingLegalTrace B values` 与 `values.length ≤ 5`：D41→D40 桥与 D13 长度语义；
* `growthRatio B values = rho5Trace` 与 `tracePeak values = rho5Trace`；
* 全局比较：每个真实非零矩阵的每条原 `LegalTrace` 增长比 `≤ growthRatio B values`。

所有合取项都是结论；`IsSign s`、`LeadingTracePos`、非零性、全局比较都不作为前提。 -/
theorem exists_canonical_representative :
    ∃ (A B : Matrix5) (s : Fin 5 → ℝ) (values : List ℝ),
      matrixEntryMax A = 1 ∧ A ≠ 0 ∧
        Rho5.TraceSigns.IsSign s ∧ B = Rho5.TraceSigns.signedEntries A s 1 ∧
          matrixEntryMax B = 1 ∧ B ≠ 0 ∧ B 0 0 = 1 ∧
            Rho5.LeadingSigns.LeadingTracePos B values ∧
              Rho5.LeadingTrace.LeadingLegalTrace B values ∧ values.length ≤ 5 ∧
                Rho5.GrowthModel.growthRatio B values = Rho5.GrowthSupremum.rho5Trace ∧
                  Rho5.GrowthModel.tracePeak values = Rho5.GrowthSupremum.rho5Trace ∧
                    ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
                      Rho5.CompletePivotPath.LegalTrace N ws →
                        Rho5.GrowthModel.growthRatio N ws ≤
                          Rho5.GrowthModel.growthRatio B values := by
  obtain ⟨A, hmaxA, hAne, values, hleading, hratioA, -⟩ := exists_normalized_leading_maximizer
  obtain ⟨s, hs, hpos⟩ := Rho5.LeadingSigns.exists_signs_leadingTracePos hleading
  have hsign1 : Rho5.TraceSigns.IsSign (1 : Fin 5 → ℝ) := fun _ => Or.inl rfl
  have hBne : Rho5.TraceSigns.signedEntries A s 1 ≠ 0 := by
    rw [← Rho5.TraceSigns.signedEntries5_eq_signedEntries' A s 1]
    exact Rho5.TraceSigns.signedEntries5_ne_zero_of_ne_zero hs hsign1 hAne
  have hmaxB : matrixEntryMax (Rho5.TraceSigns.signedEntries A s 1) = 1 := by
    rw [← Rho5.TraceSigns.signedEntries5_eq_signedEntries' A s 1,
      Rho5.TraceSigns.matrixEntryMax_signedEntries5 A hs hsign1, hmaxA]
  have hratioB : Rho5.GrowthModel.growthRatio (Rho5.TraceSigns.signedEntries A s 1) values
      = Rho5.GrowthSupremum.rho5Trace := by
    rw [← Rho5.TraceSigns.signedEntries5_eq_signedEntries' A s 1,
      Rho5.TraceSigns.growthRatio_signedEntries5 hs hsign1 values, hratioA]
  obtain ⟨hpos_corner, hmax_corner⟩ := leadingTracePos_step_facts hpos hBne
  have hcorner : Rho5.TraceSigns.signedEntries A s 1 0 0 = 1 := by
    have habs : |Rho5.TraceSigns.signedEntries A s 1 0 0| = 1 :=
      abs_corner_eq_one_of_isCompletePivot hmax_corner hmaxB
    rwa [abs_of_pos hpos_corner] at habs
  have hpeak : Rho5.GrowthModel.tracePeak values = Rho5.GrowthSupremum.rho5Trace := by
    rw [← Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmaxB, hratioB]
  have hlead : Rho5.LeadingTrace.LeadingLegalTrace (Rho5.TraceSigns.signedEntries A s 1) values :=
    Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos hpos
  have hlen : values.length ≤ 5 :=
    Rho5.CompletePivotPath.length_le_five (Rho5.LeadingTrace.legalTrace_of_leading hlead)
  refine ⟨A, Rho5.TraceSigns.signedEntries A s 1, s, values, hmaxA, hAne, hs, rfl,
    hmaxB, hBne, hcorner, hpos, hlead, hlen, hratioB, hpeak, ?_⟩
  intro N hN ws hws
  rw [hratioB]
  exact growthRatio_le_rho5Trace hN hws

/-- **阶段 B（下游直接消费形式）**：只需矩阵与值列表——条目最大值 `1`、非零、**首主元
`+1`**、正性前缀关系、条目长度 `≤ 5`、增长比与峰值都等于 `rho5Trace`，并带全局比较。 -/
theorem exists_canonical_maximizer :
    ∃ M : Matrix5, matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 = 1 ∧
      ∃ values : List ℝ,
        Rho5.LeadingSigns.LeadingTracePos M values ∧
          Rho5.LeadingTrace.LeadingLegalTrace M values ∧ values.length ≤ 5 ∧
            Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
              ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
                Rho5.CompletePivotPath.LegalTrace N ws →
                  Rho5.GrowthModel.growthRatio N ws ≤
                    Rho5.GrowthModel.growthRatio M values := by
  obtain ⟨-, B, -, values, -, -, -, hB, hmaxB, hBne, hcorner, hpos, hleading, hlen, hratio, -,
    hcmp⟩ := exists_canonical_representative
  exact ⟨B, hmaxB, hBne, hcorner, values, hpos, hleading, hlen, hratio, hcmp⟩

end Rho5.CanonicalMaximizer
