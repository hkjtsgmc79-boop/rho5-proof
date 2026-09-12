/-
D131 阶段 A — 无条件全局最大者接到 TS.`LeadingInput` 与 `height = rho5Trace`
================================================================================

输入（只读、已验收）：

* D96 `Rho5.Shared.FinalEndpointAssembly.exists_last_pivot_eq_rho_unconditional`
  —— 同一个 D68 排序四面实际最大者 `P`、同一张真实迹值表 `values`，**无任何额外前提**地
  带 `SortedBoundaryMaximizerFacts P values`、`0 ≤ s P ≤ t P`、四选一饱和边界、
  以及 `|Rho5.CanonicalTail.delta P| = rho5Trace`；
* D96 `four_lt_rho5Trace : 4 < rho5Trace`（由 D09 `alpha_gt_four` + D82 达到性支付）；
* D122 核心 `Rho5.ExternalTailSaturation.Basic` 的实际 `LeadingInput` 字段表。

本文件**只做组装**：把上述实际事实包的字段直接支付给 TS 的 `LeadingInput P`，
再把 `|δ P| = rho5Trace` 转成 TS 的 `height P = rho5Trace` 与 `4 < height P`。
`δ` 在两处是**同一个函数**（TS `delta M = w M - t M * s M / r M`，`w M = T2 M 1 1`；
D48 `CanonicalTail.delta A = T2 A 1 1 - t A * s A / r A`），这里显式证明该定义连接。

不声称：所有最大者都在 V43 立方体内（无 cube 前提）、`rho5 = alpha`、X 盒覆盖、
B 前缀归一化、极值存在性或局部流。头 `1`、`entryMax = 1`、四层真实完整主元、
`p/k` 严格正与 `delta ≠ 0` 全部**从实际事实包推出**，调用者不需要再提供任何一项。
-/
import Rho5.Shared.FinalEndpointAssembly.Witness
import Rho5.Shared.BoundaryMaximizer
import Rho5.Shared.CanonicalTail
import Rho5.ExternalTailSaturation.Basic

noncomputable section
namespace Rho5.Shared.GlobalXBMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- TS 的 `delta` 与 D48 的 `CanonicalTail.delta` 是**同一个函数**：两处都是
`T2 M 1 1 - t M * s M / r M`（TS 侧的 `w M` 就是 `T2 M 1 1`）。 -/
theorem ts_delta_eq_canonicalTail_delta (M : Matrix5) :
    Rho5.ExternalTailSaturation.delta M = Rho5.CanonicalTail.delta M := rfl

/-- TS 的 `height` 就是 D48 记号下的 `|δ|`。 -/
theorem height_eq_abs_canonicalTail_delta (M : Matrix5) :
    Rho5.ExternalTailSaturation.height M = |Rho5.CanonicalTail.delta M| := by
  rw [Rho5.ExternalTailSaturation.height, ts_delta_eq_canonicalTail_delta]

/-- `|δ M| = rho5Trace` 直接给出 TS 的第五主元非零（`4 < rho5Trace` 是无条件定理）。 -/
theorem delta_ne_of_abs_eq_rho {M : Matrix5}
    (hrho : |Rho5.CanonicalTail.delta M| = Rho5.GrowthSupremum.rho5Trace) :
    Rho5.ExternalTailSaturation.delta M ≠ 0 := by
  intro hz
  have h0 : |Rho5.CanonicalTail.delta M| = 0 := by
    rw [← ts_delta_eq_canonicalTail_delta, hz, abs_zero]
  rw [h0] at hrho
  linarith [Rho5.Shared.FinalEndpointAssembly.four_lt_rho5Trace]

/-- **核心组装**：实际排序边界最大者的事实包 + `|δ P| = rho5Trace` ⇒ 实际的
TS `LeadingInput P`。八个字段逐一由事实包字段支付，**没有**任何一个要求调用者提供。 -/
theorem leadingInput_of_sortedFacts {P : Matrix5} {values : List ℝ}
    (h : Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values)
    (hrho : |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace) :
    Rho5.ExternalTailSaturation.LeadingInput P where
  head := h.zero_zero
  cp0 := h.cp0
  cp1 := h.cp4
  cp2 := h.cp3
  cp3 := h.cp2
  p_pos := h.p_pos
  k_pos := h.k_pos
  delta_ne := delta_ne_of_abs_eq_rho hrho

/-- 同一个最大者的 TS `height` 恰为 `rho5Trace`。 -/
theorem height_eq_rho {P : Matrix5} {values : List ℝ}
    (h : Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values)
    (hrho : |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace) :
    Rho5.ExternalTailSaturation.height P = Rho5.GrowthSupremum.rho5Trace := by
  rw [height_eq_abs_canonicalTail_delta, hrho]

/-- 于是该最大者满足 TS 侧的 `4 < height`（D96 的无条件 `4 < rho5Trace`）。 -/
theorem four_lt_height {P : Matrix5} {values : List ℝ}
    (h : Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values)
    (hrho : |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace) :
    (4 : ℝ) < Rho5.ExternalTailSaturation.height P := by
  rw [height_eq_rho h hrho]
  exact Rho5.Shared.FinalEndpointAssembly.four_lt_rho5Trace

/-- **D131 阶段 A 主定理**：存在同一个实际 `P`、同一张 `values`，它同时是原全局比较下的
最大者、是 TS 的实际 `LeadingInput`、`height P = rho5Trace` 且 `4 < height P`，
并保留真实 `entryMax = 1`、真实五步 `LegalTrace`、真实 `growthRatio = rho5Trace`
与四选一饱和边界（四个面一个不少）。无额外假设。 -/
theorem exists_global_ts_maximizer :
    ∃ (P : Matrix5) (values : List ℝ),
      Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧
        Rho5.ExternalTailSaturation.LeadingInput P ∧
          Rho5.ExternalTailSaturation.height P = Rho5.GrowthSupremum.rho5Trace ∧
            (4 : ℝ) < Rho5.ExternalTailSaturation.height P ∧
              |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace ∧
                0 ≤ s P ∧ s P ≤ t P ∧
                  matrixEntryMax P = 1 ∧
                    Rho5.CompletePivotPath.LegalTrace P
                      [1, p P, k P, |r P|, Rho5.ExternalTailSaturation.height P] ∧
                      Rho5.GrowthModel.growthRatio P values = Rho5.GrowthSupremum.rho5Trace ∧
                        (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨ T2 P 1 1 = -r P) ∧
                          (∀ (M' : Matrix5), M' ≠ 0 → ∀ ws : List ℝ,
                            Rho5.CompletePivotPath.LegalTrace M' ws →
                              Rho5.GrowthModel.growthRatio M' ws ≤
                                Rho5.GrowthModel.growthRatio P values) := by
  obtain ⟨P, values, hf, hs, hst, hb, hrho⟩ :=
    Rho5.Shared.FinalEndpointAssembly.exists_last_pivot_eq_rho_unconditional
  exact ⟨P, values, hf, leadingInput_of_sortedFacts hf hrho, height_eq_rho hf hrho,
    four_lt_height hf hrho, hrho, hs, hst, hf.entryMax,
    Rho5.ExternalTailSaturation.leading_legalTrace (leadingInput_of_sortedFacts hf hrho),
    hf.growth_eq_rho, hb, hf.global_max⟩

/-- 阶段 B 的输入形态：无条件存在的实际最大者，带 TS `LeadingInput` 与 `4 < height`。 -/
theorem exists_ts_maximizer_four_lt_height :
    ∃ P : Matrix5,
      Rho5.ExternalTailSaturation.LeadingInput P ∧
        (4 : ℝ) < Rho5.ExternalTailSaturation.height P := by
  obtain ⟨P, _values, hf, hlin, _hgt, h4, _hrho, _hs, _hst, _hem, _hlg, _hgr, _hb, _hgm⟩ :=
    exists_global_ts_maximizer
  exact ⟨P, hlin, h4⟩

end Rho5.Shared.GlobalXBMaximizer
