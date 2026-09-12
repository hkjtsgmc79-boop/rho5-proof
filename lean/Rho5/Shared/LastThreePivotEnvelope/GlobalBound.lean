/-
D87 阶段 B — 全局 `rho5Trace ≤ 81/16`
=====================================

把阶段 A 的**实际** `|delta M| ≤ (9/4) · k M` 与 D86 阶段 A 冻结回执的实际前导三阶读数
（`p M`、`k M`、`r M / p M` 分别是两个**实际**三阶块的第二/第三读数）合起来，得到五个实际
值的增长上界 `81/16 = 5.0625`，再用已验收 D69 的全局等价收口到 `rho5Trace`。

链条（每一步都只有已验收上游 + 本 lane 阶段 A 作为输入）：

| 步骤 | 结论 | 来源 |
| --- | --- | --- |
| 1 | `p M ≤ 2` | D86 `leading_three_inheritance` 的 `secondPivot (firstNested M) = p M` 套 D83 包络 `secondMagnitude ≤ 2` |
| 2 | `k M ≤ 9/4` | 同上，`thirdPivot (firstNested M) = k M` 套 D83 `fixed_order_three_pivot_le_nine_quarters` |
| 3 | `r M / p M ≤ 9/4` | D86 的 `thirdPivot (secondNested M) = r M / p M` 套同一条 D83 定理 |
| 4 | `r M ≤ 9/2` | 步骤 1 + 3：`r M ≤ (9/4) · p M ≤ (9/4) · 2` |
| 5 | `|delta M| ≤ 81/16` | 阶段 A 的 `(9/4) · k M` 与步骤 2 |
| 6 | `tracePeak [1, p, k, r, |delta|] ≤ 81/16` | 步骤 1–5（五值全覆盖） |
| 7 | `growthRatio M [1, p, k, r, |delta|] ≤ 81/16` | `PolyCP` 给出 `matrixEntryMax M = 1` |
| 8 | `C M ≤ (81/16) B M ∧ |det M| ≤ (81/16) C M` | D67 `threshold_iff`（`81/16 ≥ 4`） |
| 9 | `rho5Trace ≤ 81/16` | D69 `rho5Trace_le_iff_polyCP_inequalities` 的逆向 |

**未付 / 未声称**：不重复 D86 的 `r ≤ 4`；不声称尖锐 `alpha`、不声称 `rho = alpha`、不声称
最大值可达。最终定理**没有**任何额外输入假设——量词就是 `∀ M, M 0 0 = 1 → PolyCP M → …`，
轨迹规范化与 `LegalTrace` 存在性都在 D69 已验收的等价里付清。

D86 只消费**冻结的阶段 A 细分模块**（`Rho5.Shared.NestedThreePivot.{Defs,StageA}`，oleans
与 `LEADING_THREE_READY.json` 的哈希逐字节相同）；D86 的活动 aggregate/Audit 从不被读。
-/
import Rho5.Shared.LastThreePivotEnvelope.StageA
import Rho5.Shared.NestedThreePivot.StageA
import Rho5.Shared.MinorGrowthThreshold.Threshold
import Rho5.Shared.GlobalMinorReduction.Main

namespace Rho5.LastThreePivotEnvelope

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S3 S4 T2 p k r s t)

/-! ## 0. D86 的阶段 A 记号与 D83 的记号是同一批定义（`rfl` 级桥接）

D86 在自己的 lane 里独立定义了 `secondPivot` / `thirdPivot` / `LeadingThreeNormalized`
（当时 D83 尚未编译）。三者与 D83 的 `secondMagnitude` / `thirdMagnitude` /
`FixedOrderNormalized3` 逐字同式，所以桥接就是 `rfl` / `Iff.rfl`——显式记录下来，避免
下游依赖隐式展开。 -/

theorem nested_secondPivot_eq_secondMagnitude (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Rho5.NestedThreePivot.secondPivot A = Rho5.ExternalThreePivot.secondMagnitude A := rfl

theorem nested_thirdPivot_eq_thirdMagnitude (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Rho5.NestedThreePivot.thirdPivot A = Rho5.ExternalThreePivot.thirdMagnitude A := rfl

theorem nested_normalized_iff_d83 (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Rho5.NestedThreePivot.LeadingThreeNormalized A ↔
      Rho5.ExternalThreePivot.FixedOrderNormalized3 A :=
  Iff.rfl

/-! ## 1. 三个实际主元的上界 -/

/-- **第一主元上界**：`p M ≤ 2`。
实际 `M` 的 leading `3 × 3` 的第二读数就是 `p M`，D83 的矩阵包络给出第二读数 `≤ 2`。 -/
theorem p_le_two (M : Matrix5) (h00 : M 0 0 = 1) (hCP : Rho5.MinorCPDomain.PolyCP M) :
    p M ≤ 2 := by
  obtain ⟨hnorm, hsecond, -, -, -, -⟩ := Rho5.NestedThreePivot.leading_three_inheritance M h00 hCP
  have hnorm' : Rho5.ExternalThreePivot.FixedOrderNormalized3
      (Rho5.NestedThreePivot.firstNested M) :=
    (nested_normalized_iff_d83 _).mp hnorm
  have hsecond' : Rho5.ExternalThreePivot.secondMagnitude
      (Rho5.NestedThreePivot.firstNested M) = p M := by
    rw [← nested_secondPivot_eq_secondMagnitude]
    exact hsecond
  rw [← hsecond']
  exact (Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope
    _ hnorm').2.1

/-- **第二主元上界**：`k M ≤ 9/4`。
实际 `S3 M` 的首主元 `k M` 就是 `M` 的 leading `3 × 3` 的第三读数，D83 的锐界给 `9/4`。 -/
theorem k_le_nine_quarters (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) : k M ≤ (9 : ℝ) / 4 := by
  obtain ⟨hnorm, -, hthird, -, -, -⟩ := Rho5.NestedThreePivot.leading_three_inheritance M h00 hCP
  have hnorm' : Rho5.ExternalThreePivot.FixedOrderNormalized3
      (Rho5.NestedThreePivot.firstNested M) :=
    (nested_normalized_iff_d83 _).mp hnorm
  have hthird' : Rho5.ExternalThreePivot.thirdMagnitude
      (Rho5.NestedThreePivot.firstNested M) = k M := by
    rw [← nested_thirdPivot_eq_thirdMagnitude]; exact hthird
  have h := Rho5.ExternalThreePivot.fixed_order_three_pivot_le_nine_quarters
    (Rho5.NestedThreePivot.firstNested M) hnorm'
  rwa [hthird'] at h

/-- **头两个主元之商**：`r M / p M ≤ 9/4`。
`S4 M` 的 leading `3 × 3` 除以 `p M` 的第三读数就是 `r M / p M`。 -/
theorem r_div_p_le_nine_quarters (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) : r M / p M ≤ (9 : ℝ) / 4 := by
  obtain ⟨-, -, -, hnorm2, -, hthird2⟩ :=
    Rho5.NestedThreePivot.leading_three_inheritance M h00 hCP
  have hnorm2' : Rho5.ExternalThreePivot.FixedOrderNormalized3
      (Rho5.NestedThreePivot.secondNested M) :=
    (nested_normalized_iff_d83 _).mp hnorm2
  have hthird2' : Rho5.ExternalThreePivot.thirdMagnitude
      (Rho5.NestedThreePivot.secondNested M) = r M / p M := by
    rw [← nested_thirdPivot_eq_thirdMagnitude]; exact hthird2
  have h := Rho5.ExternalThreePivot.fixed_order_three_pivot_le_nine_quarters
    (Rho5.NestedThreePivot.secondNested M) hnorm2'
  rwa [hthird2'] at h

/-- **第三主元上界**：`r M ≤ 9/2`。
由 `r M / p M ≤ 9/4` 与 `p M > 0` 得 `r M ≤ (9/4) · p M`，再与 `p M ≤ 2` 相乘。 -/
theorem r_le_nine_halves (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) : r M ≤ (9 : ℝ) / 2 := by
  obtain ⟨-, -, -, -, -, hp, -, -⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  have h1 : r M ≤ (9 : ℝ) / 4 * p M :=
    (div_le_iff₀ hp).mp (r_div_p_le_nine_quarters M h00 hCP)
  have h2 : (9 : ℝ) / 4 * p M ≤ (9 : ℝ) / 4 * 2 :=
    mul_le_mul_of_nonneg_left (p_le_two M h00 hCP) (by norm_num)
  linarith

/-! ## 2. `delta` 的实际上界 -/

/-- **阶段 A 的实际含义**：`|delta M| ≤ 81/16`。由阶段 A 的 `(9/4) · k M` 与 `k M ≤ 9/4`。 -/
theorem delta_abs_le_eighty_one_sixteenth (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    |Rho5.CanonicalTail.delta M| ≤ (81 : ℝ) / 16 := by
  calc |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M :=
        delta_abs_le_nine_quarters_mul_k M h00 hCP
    _ ≤ (9 : ℝ) / 4 * ((9 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (k_le_nine_quarters M h00 hCP) (by norm_num)
    _ = (81 : ℝ) / 16 := by norm_num

/-! ## 3. 五个实际值的增长上界 -/

/-- **五值增长 ≤ 81/16**：`1`、`p M`、`k M`、`r M`、`|delta M|` 全部被同一个常数控制。 -/
theorem five_value_peak_le_eighty_one_sixteenth (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.GrowthModel.tracePeak [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|]
      ≤ (81 : ℝ) / 16 := by
  have hp2 : p M ≤ 2 := p_le_two M h00 hCP
  have hk94 : k M ≤ (9 : ℝ) / 4 := k_le_nine_quarters M h00 hCP
  have hr92 : r M ≤ (9 : ℝ) / 2 := r_le_nine_halves M h00 hCP
  have hd : |Rho5.CanonicalTail.delta M| ≤ (81 : ℝ) / 16 :=
    delta_abs_le_eighty_one_sixteenth M h00 hCP
  refine Rho5.GrowthModel.tracePeak_le (B := (81 : ℝ) / 16) (by norm_num) ?_
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · linarith
  · linarith
  · linarith
  · exact hd

/-- **增长比 ≤ 81/16**：`PolyCP` 给出 `matrixEntryMax M = 1`，所以增长比就是五值峰值。 -/
theorem growthRatio_le_eighty_one_sixteenth (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.GrowthModel.growthRatio M [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|]
      ≤ (81 : ℝ) / 16 := by
  obtain ⟨hmax, -, -, -, -, -, -, -⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  rw [Rho5.GrowthModel.growthRatio_eq, hmax, div_one]
  exact five_value_peak_le_eighty_one_sixteenth M h00 hCP

/-! ## 4. 两条实际多项式不等式与全局收口 -/

/-- **两条子式不等式**（D67 阈值形式）：`C M ≤ (81/16) B M` 与 `|det M| ≤ (81/16) C M`。 -/
theorem polyCP_inequalities_eighty_one_sixteenth (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.MinorGrowthThreshold.C M ≤ (81 : ℝ) / 16 * Rho5.MinorGrowthThreshold.B M ∧
      |M.det| ≤ (81 : ℝ) / 16 * Rho5.MinorGrowthThreshold.C M := by
  obtain ⟨hmax, hcp0, hcp4, hcp3, -, hp, hk, hr⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  exact (Rho5.MinorGrowthThreshold.threshold_iff hmax h00 hcp0 hcp4 hcp3 hp hk hr
    (by norm_num : (4 : ℝ) ≤ 81 / 16)).mp
    (growthRatio_le_eighty_one_sixteenth M h00 hCP)

/-- **D87 阶段 B 目标**：`rho5Trace ≤ 81/16 = 5.0625`，对每一个满足 `M 0 0 = 1` 与
`PolyCP M` 的矩阵都没有额外输入假设。

这是从已验收的 `rho5Trace < 10.1` 向真实 `rho5Trace ≤ 81/16` 的一步；它**不是**尖锐
`alpha`，也**不**声称 `rho = alpha`——D69 的等价只把全局上界化为有限 `PolyCP` 域上的两条
不等式，而这两条在这里由实际五值界付清。 -/
theorem rho5Trace_le_eighty_one_sixteenth :
    Rho5.GrowthSupremum.rho5Trace ≤ (81 : ℝ) / 16 := by
  refine (Rho5.GlobalMinorReduction.rho5Trace_le_iff_polyCP_inequalities
    (by norm_num : (4 : ℝ) ≤ 81 / 16)).mpr ?_
  intro M h00 hCP
  exact polyCP_inequalities_eighty_one_sixteenth M h00 hCP

/-- 数值记录：`81/16 = 5.0625 < 10.1`，即本结果是已验收 `rho < 10.1` 的实质改进。 -/
theorem eighty_one_sixteenth_lt_ten_point_one : (81 : ℝ) / 16 < 10.1 := by norm_num

/-- 把目标与改进一起记录（`rho5Trace ≤ 81/16 < 10.1`）。 -/
theorem rho5Trace_le_eighty_one_sixteenth_and_improves :
    Rho5.GrowthSupremum.rho5Trace ≤ (81 : ℝ) / 16 ∧ (81 : ℝ) / 16 < 10.1 :=
  ⟨rho5Trace_le_eighty_one_sixteenth, eighty_one_sixteenth_lt_ten_point_one⟩

end Rho5.LastThreePivotEnvelope
