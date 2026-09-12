/-
D90 目标 D — 真实最后主元最大见证（同一个 D68 排序四面最大者）
==============================================================

`4 < rho5Trace` 时，D68_FULL 已验收的排序四面最大者 `P`（带真实迹值表
`values = [1, p P, k P, r P, |δ P|]`）满足

    `|δ P| = rho5Trace`：

* `|δ P| ≤ rho5Trace`：`|δ P|` 是迹值的成员，`le_tracePeak` 直接给出；
* `rho5Trace ≤ |δ P|`：峰值同时受 `max 4 |δ P|` 控制——因为 `1 ≤ 4`、`p P ≤ 2 ≤ 4`、
  `k P ≤ 4`、`r P ≤ 4`（后三条由 D86 已验收的 `fourth_pivot_envelope` 给出，
  `p ≤ 2` 与 `k/p ≤ 2` 合成 `k ≤ 4`），所以早期峰值全部 ≤ 4；由 `4 < rho5Trace` 得
  `4 < max 4 |δ P|`，于是 `max 4 |δ P| = |δ P|`。

**保持原 `M` 与全部四个面**：结论里仍是 D68 的同一个 `P`、同一张迹值表、同一条
`0 ≤ s P ≤ t P` 与同一个四选一饱和边界析取；不假设平衡、不换成第二个对象、
不添加 `r ≤ 4` 之外的新前提，也不把「最后主元主导」当作调用方假设。

本结论只在 `4 < rho5Trace` 这个**已验收存在的区间**上说话：它不声称 `4 < rho5Trace`
本身（那是 D44/其他卡的读数），也不声称最大值在别处可达。
无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Rho5.Shared.LastPivotUpperReduction.Common
import Rho5.Shared.BoundaryMaximizer
import Rho5.Shared.GrowthModel
import Rho5.Shared.CanonicalTail
import Mathlib.Order.Lattice
import Mathlib.Tactic.Linarith

namespace Rho5.LastPivotUpperReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.MinorCPDomain (PolyCP)

/-- **D90 目标 D**：`4 < rho5Trace` 时，D68 的排序四面最大者的**真实最后主元**
`|δ P|` 就等于 `rho5Trace`。原 `P`、原迹值表、四个饱和面全部保留。 -/
theorem exists_last_pivot_eq_rho (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (P : Matrix5) (values : List ℝ),
      Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧ 0 ≤ s P ∧ s P ≤ t P ∧
        (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨ T2 P 1 1 = -r P) ∧
          |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace := by
  obtain ⟨P, values, hfacts, hs, hst, hbound⟩ :=
    Rho5.BoundaryMaximizer.exists_sorted_boundary_maximizer_four_faces h4
  have h00 : P 0 0 = 1 := hfacts.zero_zero
  have hpoly : PolyCP P :=
    (Rho5.MinorCPDomain.polyCP_iff_frame P h00).mpr
      ⟨hfacts.entryMax, hfacts.cp0, hfacts.cp4, hfacts.cp3, hfacts.cp2,
        hfacts.p_pos, hfacts.k_pos, hfacts.r_pos⟩
  -- 峰值就是 `rho5Trace`（单位 entry-max 下增长比即峰值，D68 的 `growth_eq_rho`）
  have hpeak : Rho5.GrowthModel.tracePeak values = Rho5.GrowthSupremum.rho5Trace := by
    rw [← Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hfacts.entryMax,
      hfacts.growth_eq_rho]
  -- 最后主元是迹值成员，故 `|δ P| ≤ rho5Trace`
  have hmem : |Rho5.CanonicalTail.delta P| ∈ values := by
    rw [hfacts.trace_eq]
    simp
  have hle : |Rho5.CanonicalTail.delta P| ≤ Rho5.GrowthSupremum.rho5Trace :=
    (Rho5.GrowthModel.le_tracePeak hmem).trans_eq hpeak
  -- D86 实际包络：`p ≤ 2`、`k/p ≤ 2`（合成 `k ≤ 4`）、`r ≤ 4`
  have henv := Rho5.NestedThreePivot.fourth_pivot_envelope P h00 hpoly
  have hp : 0 < p P := henv.1
  have hp2 : p P ≤ 2 := henv.2.1
  have hkp2 : k P / p P ≤ 2 := henv.2.2.2.1
  have hr4 : r P ≤ 4 := henv.2.2.2.2.2.2
  have hk4 : k P ≤ 4 := by
    have h1 : k P ≤ 2 * p P := (div_le_iff₀ hp).mp hkp2
    calc k P ≤ 2 * p P := h1
      _ ≤ 2 * 2 := by linarith
      _ = 4 := by norm_num
  -- 峰值受 `max 4 |δ P|` 控制：早期四个读数都 ≤ 4
  have hb4 : Rho5.GrowthSupremum.rho5Trace ≤ max (4 : ℝ) |Rho5.CanonicalTail.delta P| := by
    rw [← hpeak]
    refine Rho5.GrowthModel.tracePeak_le (le_max_of_le_left (by norm_num)) ?_
    intro v hv
    rw [hfacts.trace_eq] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact le_trans (by norm_num : (1 : ℝ) ≤ 4) (le_max_left 4 _)
    · exact le_trans hp2 (le_trans (by norm_num : (2 : ℝ) ≤ 4) (le_max_left 4 _))
    · exact le_trans hk4 (le_max_left 4 _)
    · exact le_trans hr4 (le_max_left 4 _)
    · exact le_max_right 4 _
  have hgt : (4 : ℝ) < max (4 : ℝ) |Rho5.CanonicalTail.delta P| := lt_of_lt_of_le h4 hb4
  have h4δ : (4 : ℝ) < |Rho5.CanonicalTail.delta P| := by
    rcases lt_max_iff.mp hgt with h | h
    · exact absurd h (lt_irrefl 4)
    · exact h
  have hge : Rho5.GrowthSupremum.rho5Trace ≤ |Rho5.CanonicalTail.delta P| := by
    rw [max_eq_right (le_of_lt h4δ)] at hb4
    exact hb4
  exact ⟨P, values, hfacts, hs, hst, hbound, le_antisymm hle hge⟩

end Rho5.LastPivotUpperReduction
