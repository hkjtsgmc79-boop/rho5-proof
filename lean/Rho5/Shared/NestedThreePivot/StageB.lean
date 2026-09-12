/-
D86 阶段 B — 第四主元 `r ≤ 4`（消费 D83/D85 已验收包络）
============================================================

阶段 A（`StageA.lean`）已在 `M 0 0 = 1` 与 `PolyCP M` 下支付了两个实际 `3 × 3` 的
固定顺序归一化资格与精确读数。本文件在同一 lane 内**只做桥接与组装**：

1. 桥接：`LeadingThreeNormalized = ExternalThreePivot.FixedOrderNormalized3`、
   `secondPivot = secondMagnitude`、`thirdPivot = thirdMagnitude`（三者同式，`defeq`/`rfl`）；
2. 对 `firstNested M` 用 D83 已验收的 `fixed_order_three_pivot_envelope` 得
   `p M ≤ 2` 与 `k M ≤ phi (p M)`；
3. 对 `secondNested M` 用同一包络得 `k M / p M ≤ 2` 与 `r M / p M ≤ phi (k M / p M)`，
   即 `r M ≤ p M * phi (k M / p M)`；
4. 用 D85 已验收的 `double_envelope_le_four`（`p := p M`、`t := k M / p M`）闭合到
   `r M ≤ 4`。`phi` 的 if 展开由本文件自己一行 `rfl` 完成（不新建同名 `phi` 定义）。

**不声称**：`4 < rho5Trace`、满秩、`d = -r`、全域可平衡、`rho5 = alpha`、最大值可达；
不重编 D83/D85，不重审上游。最终语句只接受 `M 0 0 = 1` 与 `PolyCP M`。 -/
import Rho5.Shared.NestedThreePivot.StageA
import Rho5.ExternalThreePivot
import Rho5.Shared.DoubleThreePivotEnvelope

namespace Rho5.NestedThreePivot

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)
open Rho5.MinorCPDomain (PolyCP)

/-- **D86 阶段 B 主定理（实际 `r ≤ 4`）**：`M 0 0 = 1` 且 `PolyCP M` 时第四主元读数
`r M` 不超过 `4`。前提只有归一化与实际多项式 CP 域，既不含 `r ≤ 4`，也不含任何包络、
子块资格或高支预算假设。 -/
theorem fourth_pivot_le_four (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) : r M ≤ 4 := by
  obtain ⟨hA1, hsm1, htm1, hA2, hsm2, htm2⟩ := leading_three_inheritance M h00 hP
  -- 桥接：本 lane 的定义与 D83 包络的定义同式
  have hF1 : Rho5.ExternalThreePivot.FixedOrderNormalized3 (firstNested M) := hA1
  have hF2 : Rho5.ExternalThreePivot.FixedOrderNormalized3 (secondNested M) := hA2
  have hSM1 : Rho5.ExternalThreePivot.secondMagnitude (firstNested M) = p M := hsm1
  have hTM1 : Rho5.ExternalThreePivot.thirdMagnitude (firstNested M) = k M := htm1
  have hSM2 : Rho5.ExternalThreePivot.secondMagnitude (secondNested M) = k M / p M := hsm2
  have hTM2 : Rho5.ExternalThreePivot.thirdMagnitude (secondNested M) = r M / p M := htm2
  -- D83：两个实际矩阵各自的尖锐三主元包络
  obtain ⟨-, hp2, hkphi⟩ :=
    Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope (firstNested M) hF1
  obtain ⟨-, hkp2, hrphi⟩ :=
    Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope (secondNested M) hF2
  have hp2' : p M ≤ 2 := by rwa [hSM1] at hp2
  have hkphi' : k M ≤ Rho5.ExternalThreePivot.phi (p M) := by rwa [hSM1, hTM1] at hkphi
  have hkp2' : k M / p M ≤ 2 := by rwa [hSM2] at hkp2
  have hrphi' : r M / p M ≤ Rho5.ExternalThreePivot.phi (k M / p M) := by
    rwa [hSM2, hTM2] at hrphi
  -- PolyCP 给出的正性与导出读数
  obtain ⟨hA, hB, hC, -, -, -, -⟩ := hP
  have hp : 0 < p M := by
    rw [← Rho5.MinorCPDomain.A_eq M h00]
    exact hA
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hk : 0 < k M := by
    have hB' : 0 < p M * k M := by
      rw [← Rho5.MinorCPDomain.B_eq M h00 hpne]
      exact hB
    have hB'' : 0 < k M * p M := by
      rw [mul_comm]; exact hB'
    exact pos_of_mul_pos_left hB'' (le_of_lt hp)
  have hr : 0 < r M := by
    have hC' : 0 < p M * k M * r M := by
      rw [← Rho5.MinorCPDomain.C_eq M h00 hp hk]
      exact hC
    exact pos_of_mul_pos_right hC' (le_of_lt (mul_pos hp hk))
  have hkp0 : 0 ≤ k M / p M := le_of_lt (div_pos hk hp)
  -- `phi` 的显式 if 展开（一行 `rfl`，不新建同名定义）
  have hphi_p : Rho5.ExternalThreePivot.phi (p M)
      = (if p M ≤ 1 then 2 * p M else p M * (3 - p M)) := rfl
  have hphi_t : Rho5.ExternalThreePivot.phi (k M / p M)
      = (if k M / p M ≤ 1 then 2 * (k M / p M)
          else (k M / p M) * (3 - k M / p M)) := rfl
  -- D85 的乘积前提：`p * (k / p) = k ≤ phi p`
  have hprod : p M * (k M / p M)
      ≤ (if p M ≤ 1 then 2 * p M else p M * (3 - p M)) := by
    have hmul : p M * (k M / p M) = k M := by
      field_simp
    rw [hmul, ← hphi_p]
    exact hkphi'
  have h4 := Rho5.DoubleThreePivotEnvelope.double_envelope_le_four (p M) (k M / p M)
    (le_of_lt hp) hp2' hkp0 hkp2' hprod
  -- `r ≤ p * phi (k / p) ≤ 4`
  have hrle : r M ≤ p M * (if k M / p M ≤ 1 then 2 * (k M / p M)
      else (k M / p M) * (3 - k M / p M)) := by
    have hthis : r M ≤ Rho5.ExternalThreePivot.phi (k M / p M) * p M :=
      (div_le_iff₀ hp).mp hrphi'
    rw [mul_comm (Rho5.ExternalThreePivot.phi (k M / p M)) (p M), hphi_t] at hthis
    exact hthis
  exact hrle.trans h4

/-- **阶段 B 的完整读数链**（同一主定理的展开形式，供下游直接消费）：

`0 < p M`、`p M ≤ 2`、`0 < k M / p M`、`k M / p M ≤ 2`、
`k M ≤ phi (p M)`、`r M ≤ p M * phi (k M / p M)`，以及 `r M ≤ 4`。 -/
theorem fourth_pivot_envelope (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) :
    0 < p M ∧ p M ≤ 2 ∧ 0 < k M / p M ∧ k M / p M ≤ 2 ∧
      k M ≤ Rho5.ExternalThreePivot.phi (p M) ∧
        r M ≤ p M * Rho5.ExternalThreePivot.phi (k M / p M) ∧ r M ≤ 4 := by
  obtain ⟨hA1, hsm1, htm1, hA2, hsm2, htm2⟩ := leading_three_inheritance M h00 hP
  have hF1 : Rho5.ExternalThreePivot.FixedOrderNormalized3 (firstNested M) := hA1
  have hF2 : Rho5.ExternalThreePivot.FixedOrderNormalized3 (secondNested M) := hA2
  have hSM1 : Rho5.ExternalThreePivot.secondMagnitude (firstNested M) = p M := hsm1
  have hTM1 : Rho5.ExternalThreePivot.thirdMagnitude (firstNested M) = k M := htm1
  have hSM2 : Rho5.ExternalThreePivot.secondMagnitude (secondNested M) = k M / p M := hsm2
  have hTM2 : Rho5.ExternalThreePivot.thirdMagnitude (secondNested M) = r M / p M := htm2
  obtain ⟨-, hp2, hkphi⟩ :=
    Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope (firstNested M) hF1
  obtain ⟨-, hkp2, hrphi⟩ :=
    Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope (secondNested M) hF2
  have hp2' : p M ≤ 2 := by rwa [hSM1] at hp2
  have hkphi' : k M ≤ Rho5.ExternalThreePivot.phi (p M) := by rwa [hSM1, hTM1] at hkphi
  have hkp2' : k M / p M ≤ 2 := by rwa [hSM2] at hkp2
  have hrphi' : r M / p M ≤ Rho5.ExternalThreePivot.phi (k M / p M) := by
    rwa [hSM2, hTM2] at hrphi
  have hPc := hP
  obtain ⟨hA, hB, hC, -, -, -, -⟩ := hPc
  have hp : 0 < p M := by
    rw [← Rho5.MinorCPDomain.A_eq M h00]
    exact hA
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hk : 0 < k M := by
    have hB' : 0 < p M * k M := by
      rw [← Rho5.MinorCPDomain.B_eq M h00 hpne]
      exact hB
    have hB'' : 0 < k M * p M := by
      rw [mul_comm]; exact hB'
    exact pos_of_mul_pos_left hB'' (le_of_lt hp)
  refine ⟨hp, hp2', div_pos hk hp, hkp2', hkphi', ?_, fourth_pivot_le_four M h00 hP⟩
  calc r M ≤ Rho5.ExternalThreePivot.phi (k M / p M) * p M :=
        (div_le_iff₀ hp).mp hrphi'
    _ = p M * Rho5.ExternalThreePivot.phi (k M / p M) := mul_comm _ _

end Rho5.NestedThreePivot
