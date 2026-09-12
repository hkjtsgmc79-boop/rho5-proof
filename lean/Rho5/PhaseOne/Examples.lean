import Rho5.Integration.StagedAssembly.Conditional

/-!
# D161 — `Rho5.PhaseOne.Examples`: 第一阶段实际使用示例

本文件是**可编译的使用示例**，不是新的数学证明：每个定理都只是已验 C02 修订入口
（`Rho5.Integration.StagedAssembly.Conditional`）及其传递依赖中既有定理的直接应用或投影。
使用方式与边界见同目录交付的 `USAGE.md`。

三段内容：

1. **无条件可用**（零证明参数）：实际 α 的根身份/区间、上确界语义、实际达到、
   `α ≤ rho5Trace ≤ 81/16`、`4 < rho5Trace`、原全局最大者存在；
2. **显式条件**（恰好两个未付全域安全前提 `hX`/`hB`）：`rho5Trace = α`、
   原任意非零矩阵与原 `LegalTrace` 的增长端点、第五读数端点、行列式端点；
3. **两个安全义务的公开形状**：`XGlobalSafety` 与 `RootEndpointSafety` 的原始 Prop。

本文件**不含** `axiom`/`sorry`/`admit`/`native_decide`，也**不**提供任何无条件版本的
`rho5Trace = α`——那需要尚未完成的完整 `XGlobalSafety` 与 `RootEndpointSafety`。
-/

noncomputable section

namespace Rho5.PhaseOne.Examples

open Rho5
open Rho5.Algebraic.AlphaRoot (alpha)
open Rho5.GrowthSupremum (rho5Trace)
open Rho5.Integration.StagedAssembly (XGlobalSafety)
open Rho5.Shared.BRootCapacityEndpoint (RootEndpointSafety IsRootCapacityEndpoint)

/-! ## 1. 无条件：零证明参数即可使用 -/

/-- 实际 `α` 是 `rootPolynomial` 在 `(4,5)` 中的**唯一**根（D09 已验）。 -/
theorem alpha_unique_root_in_four_five :
    ∃! a : ℝ, 4 < a ∧ a < 5 ∧ Rho5.Algebraic.AlphaRoot.rootPolynomial a = 0 :=
  Rho5.Algebraic.AlphaRoot.exists_unique_root

/-- `α` 本身的读数：`4 < α < 5` 且 `rootPolynomial α = 0`。 -/
theorem alpha_readings :
    4 < alpha ∧ alpha < 5 ∧ Rho5.Algebraic.AlphaRoot.rootPolynomial alpha = 0 :=
  ⟨Rho5.Algebraic.AlphaRoot.alpha_gt_four, Rho5.Algebraic.AlphaRoot.alpha_lt_five,
    Rho5.Algebraic.AlphaRoot.alpha_is_root⟩

/-- 上确界语义：`rho5Trace` 就是增长值集合的上确界（D92 已验）。 -/
theorem rho5Trace_is_sSup : rho5Trace = sSup Rho5.GrowthModel.GrowthValues :=
  Rho5.Shared.GlobalAttainedWitness.rho5Trace_semantics

/-- **实际达到**：真实矩阵 `actualAlphaMatrix` 的元素最大值为 1，原 `LegalTrace` 成立，
实际增长等于 `α`，且 `α` 属于原增长值集合（D82 已验）。 -/
theorem actual_alpha_attained :
    Rho5.matrixEntryMax Rho5.ExternalAttainment.actualAlphaMatrix = 1 ∧
      Rho5.CompletePivotPath.LegalTrace Rho5.ExternalAttainment.actualAlphaMatrix
        Rho5.ExternalAttainment.actualAlphaValues ∧
      Rho5.GrowthModel.growthRatio Rho5.ExternalAttainment.actualAlphaMatrix
        Rho5.ExternalAttainment.actualAlphaValues = alpha ∧
      alpha ∈ Rho5.GrowthModel.GrowthValues := by
  obtain ⟨hm, ht, hg, hmem, -⟩ := Rho5.ExternalAttainment.actualAlpha_attainment
  exact ⟨hm, ht, hg, hmem⟩

/-- 无条件双侧界：`α ≤ rho5Trace ≤ 81/16`（粗上界，**不是** sharp α 上界）。 -/
theorem alpha_le_rho5Trace_le_eighty_one_sixteenth :
    alpha ≤ rho5Trace ∧ rho5Trace ≤ (81 : ℝ) / 16 :=
  ⟨Rho5.Shared.GlobalAttainedWitness.alpha_le_rho5Trace,
    Rho5.Shared.GlobalAttainedWitness.rho5Trace_le_eighty_one_sixteenth⟩

/-- 无条件：`4 < rho5Trace`（超过第五读数阈值的实际存在性）。 -/
theorem four_lt_rho5Trace : (4 : ℝ) < rho5Trace :=
  Rho5.Shared.GlobalAttainedWitness.four_lt_rho5Trace

/-- **原全局最大者存在**（无条件）：真实矩阵 `P`、原合法路径 `values`、同高关系与全员支配。
这是 C02 `baseline` 的存在性部分（D92/D131 已验），显式保留原矩阵与路径。 -/
theorem exists_global_maximizer :
    ∃ (P : Matrix5) (values : List ℝ),
      Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧
        Rho5.ExternalTailSaturation.LeadingInput P ∧
        Rho5.ExternalTailSaturation.height P = rho5Trace ∧
        (4 : ℝ) < Rho5.ExternalTailSaturation.height P ∧
        Rho5.matrixEntryMax P = 1 ∧
        Rho5.CompletePivotPath.LegalTrace P
          [1, Rho5.Certificate.B24Extraction.p P, Rho5.Certificate.B24Extraction.k P,
            |Rho5.Certificate.B24Extraction.r P|, Rho5.ExternalTailSaturation.height P] ∧
        Rho5.GrowthModel.growthRatio P values = rho5Trace ∧
        (∀ (M : Matrix5), M ≠ 0 → ∀ ws : List ℝ,
          Rho5.CompletePivotPath.LegalTrace M ws →
            Rho5.GrowthModel.growthRatio M ws ≤ Rho5.GrowthModel.growthRatio P values) := by
  obtain ⟨-, -, -, -, -, -, P, values, hf, hlin, hgt, h4, hem, hleg, hgr, hgm⟩ :=
    Rho5.Integration.StagedAssembly.baseline
  exact ⟨P, values, hf, hlin, hgt, h4, hem, hleg, hgr, hgm⟩

/-! ## 2. 显式条件：恰好需要两个未付全域安全前提 -/

/-- **条件 sharp 等式**（第一阶段最终逻辑总装）：在 `hX`/`hB` 下 `rho5Trace = α`。
两个参数都是公开证明参数；本文件不提供它们的任何证明，也不提供无条件版本。 -/
theorem rho5Trace_eq_alpha (hX : XGlobalSafety) (hB : RootEndpointSafety) :
    rho5Trace = alpha :=
  Rho5.Integration.StagedAssembly.rho5Trace_eq_alpha_of_safety hX hB

/-- **原 `LegalTrace` 端点**：任意非零原矩阵与其原合法路径的增长比不超过 `α`（同 `hX`/`hB`）。 -/
theorem legal_growth_le_alpha (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    Rho5.GrowthModel.growthRatio A values ≤ alpha :=
  Rho5.Integration.StagedAssembly.legal_growth_le_alpha_of_safety hX hB A values hne htrace

/-- 同一原路径的第五读数端点（D124 早停接口，经上面的增长端点）。 -/
theorem fifth_readout_le_alpha (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    values.getD 4 0 ≤ alpha * Rho5.matrixEntryMax A :=
  Rho5.Integration.StagedAssembly.fifth_readout_le_alpha_of_safety hX hB A values hne htrace

/-- 增长超过 4 时 D124 的实际第五读数识别（同一 `A`/`values`），附带条件上界。 -/
theorem high_path_fifth (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : Rho5.CompletePivotPath.LegalTrace A values)
    (hhigh : 4 < Rho5.GrowthModel.growthRatio A values) :
    values.length = 5 ∧ values.getD 4 0 = Rho5.GrowthModel.tracePeak values ∧
      4 * Rho5.matrixEntryMax A < values.getD 4 0 ∧
      values.getD 4 0 ≤ alpha * Rho5.matrixEntryMax A :=
  Rho5.Integration.StagedAssembly.high_path_fifth_of_safety hX hB A values hne htrace hhigh

/-- **行列式端点**（D96 既有等价，非新证明；同 `hX`/`hB`）。 -/
theorem det_endpoint (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (M : Matrix5) (h00 : M 0 0 = 1) (hCP : Rho5.MinorCPDomain.PolyCP M) :
    |M.det| ≤ alpha * Rho5.MinorGrowthThreshold.C M :=
  Rho5.Integration.StagedAssembly.det_endpoint_of_safety hX hB M h00 hCP

/-! ## 3. 两个安全义务的公开形状（未付；见 `USAGE.md`） -/

/-- `XGlobalSafety` 的形状：**完整** `Physical X` 域上的高度上界，无 cube/有限样本限制。 -/
theorem xGlobalSafety_shape (hX : XGlobalSafety) :
    ∀ x : Rho5.LocalAnalysis.X, Rho5.LocalAnalysis.V43.Physical x →
      Rho5.LocalAnalysis.height x ≤ alpha := hX

/-- `RootEndpointSafety` 的形状：所有原根容量端点的高度不超过 `α`（B 侧用原 D142 定义）。 -/
theorem rootEndpointSafety_shape (hB : RootEndpointSafety) :
    ∀ zStar : Rho5.Certificate.B16.Point, IsRootCapacityEndpoint zStar →
      zStar 23 ≤ alpha := hB

/-- 使用示例：给定两个安全证明，任意非零原矩阵/合法路径都满足 `growthRatio ≤ α`
（`example` 形式，展示调用方式）。 -/
example (hX : XGlobalSafety) (hB : RootEndpointSafety) (A : Matrix5) (values : List ℝ)
    (hne : A ≠ 0) (htrace : Rho5.CompletePivotPath.LegalTrace A values) :
    Rho5.GrowthModel.growthRatio A values ≤ alpha :=
  legal_growth_le_alpha hX hB A values hne htrace

/-- 使用示例：条件等式本身。 -/
example (hX : XGlobalSafety) (hB : RootEndpointSafety) : rho5Trace = alpha :=
  rho5Trace_eq_alpha hX hB

end Rho5.PhaseOne.Examples
