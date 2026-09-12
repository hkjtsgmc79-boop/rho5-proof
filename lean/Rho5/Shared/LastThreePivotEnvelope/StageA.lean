/-
D87 阶段 A — 实际最后三阶包络：主定理
=====================================

把 D83 已验收的具名矩阵包络

  `Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope`
    `(A : Matrix3) (hA : FixedOrderNormalized3 A) :`
    `0 ≤ secondMagnitude A ∧ secondMagnitude A ≤ 2 ∧ thirdMagnitude A ≤ phi (secondMagnitude A)`

应用到**实际**矩阵 `A3 = scaledS3 M = (k M)⁻¹ • S3 M`，其中 `M` 是真实的 `5 × 5` 矩阵，
`M 0 0 = 1` 且 `PolyCP M`。

为此要付清三件事，全部由已验收上游按哈希绑定复用：

1. **实际 Schur 链与冻结固定顺序更新一致**（`S4`/`S3`/`T2` 的 `pivotSchur · 0 0` 就是
   `Rho5.Pivot.fixedSchur`，D37 的 `S3_zero_zero` + D10 的 `movePivot_zero_zero_eq`）；
2. **D48 的 `delta` 就是 `fixedSchur (T2 M) 0 0`**（D48 的 `delta_eq_pivotSchur`）；
3. **线性缩放的 Schur 律**（D08 的 `fixedSchur_smul`）把 `(k M)⁻¹ •` 从 `S3` 传到
   `T2` 与末位 `1 × 1`，且**缩放不改变完整主元资格**（D08 的 `isCompletePivot_smul_iff`）。

结论（全部无条件于尾部增长、无条件于 `delta` 符号）：

* `FixedOrderNormalized3 (scaledS3 M)`；
* `secondMagnitude (scaledS3 M) = r M / k M`；
* `thirdMagnitude (scaledS3 M) = |delta M| / k M`；
* `|delta M| ≤ k M * phi (r M / k M)`；
* `|delta M| ≤ (9 : ℝ) / 4 * k M`。

**未付 / 未声称**：没有任何尾部增长假设，没有「五个主元全非零」，没有 `r ≤ 4`，
没有 `rho5Trace ≤ 81/16`（阶段 B）。`delta M = 0`、`delta M < 0`、`0 < delta M` 三种真实
情形都由同一条绝对值结论覆盖，并各有具名推论。
-/
import Rho5.Shared.LastThreePivotEnvelope.Defs

namespace Rho5.LastThreePivotEnvelope

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S3 S4 T2 p k r s t)

/-! ## 1. 实际 Schur 链与冻结固定顺序更新一致 -/

/-- 第一次更新：`S4 M` 就是冻结的固定顺序 `fixedSchur M`。 -/
theorem S4_eq_fixedSchur (M : Matrix5) : S4 M = Rho5.Pivot.fixedSchur M := by
  simp only [S4, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- 第二次更新：`S3 M = fixedSchur (S4 M)`。 -/
theorem S3_eq_fixedSchur (M : Matrix5) : S3 M = Rho5.Pivot.fixedSchur (S4 M) := by
  simp only [S3, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- 第三次更新：`T2 M = fixedSchur (S3 M)`。 -/
theorem T2_eq_fixedSchur (M : Matrix5) : T2 M = Rho5.Pivot.fixedSchur (S3 M) := by
  simp only [T2, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- **D48 的 `delta` 就是末位 `1 × 1` 块的固定顺序读数**：`delta M = fixedSchur (T2 M) 0 0`。
这一步把卡上记号 `δ = d - t s / r`（D48 Defs）接到本 lane 使用的冻结 `fixedSchur` 上，
没有重推 D48 的任何内容。 -/
theorem delta_eq_fixedSchur (M : Matrix5) :
    Rho5.CanonicalTail.delta M = Rho5.Pivot.fixedSchur (T2 M) 0 0 := by
  simp only [Rho5.CanonicalTail.delta_eq_pivotSchur, Rho5.PivotReindex.pivotSchur,
    Rho5.PivotReindex.movePivot_zero_zero_eq]

/-! ## 2. 归一化块的条目与主元读数 -/

/-- `A3` 的条目形式。 -/
theorem scaledS3_apply (M : Matrix5) (i j : Fin 3) :
    scaledS3 M i j = (k M)⁻¹ * S3 M i j :=
  Rho5.MatrixNormalization.smul_apply_entry (k M)⁻¹ (S3 M) i j

/-- `A3` 的首主元恰为 `1`（这正是 D83 结构 `FixedOrderNormalized3` 的第二项）。 -/
theorem scaledS3_zero_zero (M : Matrix5) (hk : k M ≠ 0) : scaledS3 M 0 0 = 1 := by
  rw [scaledS3_apply, ← k, inv_mul_cancel₀ hk]

/-- `A3` 的 25→9 个条目界：由 `S3 M` 的完整主元资格（`PolyCP` 的第三个前导完整主元）
与 `k M > 0` 付清。**没有**使用 `delta` 的任何信息。 -/
theorem abs_scaledS3_le_one (M : Matrix5) (hk : 0 < k M)
    (hcp : Rho5.Pivot.IsCompletePivot (S3 M) 0 0) (i j : Fin 3) :
    |scaledS3 M i j| ≤ 1 := by
  have hkne : k M ≠ 0 := ne_of_gt hk
  have hbase : |S3 M 0 0| = k M := by
    rw [Rho5.Certificate.B24Extraction.S3_zero_zero M, abs_of_pos hk]
  have h1 : |S3 M i j| ≤ k M := by
    have h := hcp i j
    rwa [hbase] at h
  rw [scaledS3_apply, abs_mul, abs_inv, abs_of_pos hk]
  calc (k M)⁻¹ * |S3 M i j| ≤ (k M)⁻¹ * k M :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hk.le)
    _ = 1 := inv_mul_cancel₀ hkne

/-- **缩放的 Schur 律（第一步）**：`fixedSchur (A3) = (k M)⁻¹ • T2 M`。
用 D08 的 `fixedSchur_smul`；两个资格 `(k M)⁻¹ ≠ 0` 与 `S3 M 0 0 ≠ 0` 都由 `k M > 0` 付清。 -/
theorem scaledS3_fixedSchur (M : Matrix5) (hk : 0 < k M) :
    Rho5.Pivot.fixedSchur (scaledS3 M) = (k M)⁻¹ • T2 M := by
  have hkne : k M ≠ 0 := ne_of_gt hk
  have hA : S3 M 0 0 ≠ 0 := by
    rw [Rho5.Certificate.B24Extraction.S3_zero_zero M]; exact hkne
  rw [scaledS3, Rho5.MatrixNormalization.fixedSchur_smul (S3 M) (inv_ne_zero hkne) hA,
    ← T2_eq_fixedSchur]

/-- **缩放的 Schur 律（第二步，末位 `1 × 1`）**：
`fixedSchur (fixedSchur (A3)) = (k M)⁻¹ • fixedSchur (T2 M)`。这里需要第三个主元 `r M > 0`
作为 `T2 M` 的有效主元资格（不是尾部增长结论）。 -/
theorem scaledS3_fixedSchur_fixedSchur (M : Matrix5) (hk : 0 < k M) (hr : 0 < r M) :
    Rho5.Pivot.fixedSchur (Rho5.Pivot.fixedSchur (scaledS3 M))
      = (k M)⁻¹ • Rho5.Pivot.fixedSchur (T2 M) := by
  have hkne : k M ≠ 0 := ne_of_gt hk
  have hrne : r M ≠ 0 := ne_of_gt hr
  have hA : T2 M 0 0 ≠ 0 := by rw [← r]; exact hrne
  rw [scaledS3_fixedSchur M hk,
    Rho5.MatrixNormalization.fixedSchur_smul (T2 M) (inv_ne_zero hkne) hA]

/-- **第二读数**：`secondMagnitude (A3) = r M / k M`。 -/
theorem secondMagnitude_scaledS3 (M : Matrix5) (hk : 0 < k M) (hr : 0 < r M) :
    Rho5.ExternalThreePivot.secondMagnitude (scaledS3 M) = r M / k M := by
  have hmain : Rho5.ExternalThreePivot.secondMagnitude (scaledS3 M) = (k M)⁻¹ * r M := by
    rw [Rho5.ExternalThreePivot.secondMagnitude, scaledS3_fixedSchur M hk,
      Rho5.MatrixNormalization.smul_apply_entry, show T2 M 0 0 = r M from rfl,
      abs_mul, abs_inv, abs_of_pos hk, abs_of_pos hr]
  rw [hmain, div_eq_inv_mul]

/-- **第三读数**：`thirdMagnitude (A3) = |delta M| / k M`。
末位读数的停机分支在这里**不触发**（`fixedSchur (A3) 0 0 = (k M)⁻¹ * r M ≠ 0`，因为
`r M > 0`），所以 `delta M` 的符号与是否为零都不影响这条恒等式。 -/
theorem thirdMagnitude_scaledS3 (M : Matrix5) (hk : 0 < k M) (hr : 0 < r M) :
    Rho5.ExternalThreePivot.thirdMagnitude (scaledS3 M)
      = |Rho5.CanonicalTail.delta M| / k M := by
  have hkne : k M ≠ 0 := ne_of_gt hk
  have hrne : r M ≠ 0 := ne_of_gt hr
  have hne : Rho5.Pivot.fixedSchur (scaledS3 M) 0 0 ≠ 0 := by
    rw [scaledS3_fixedSchur M hk, Rho5.MatrixNormalization.smul_apply_entry,
      show T2 M 0 0 = r M from rfl]
    exact mul_ne_zero (inv_ne_zero hkne) hrne
  have hmain : Rho5.ExternalThreePivot.thirdMagnitude (scaledS3 M)
      = (k M)⁻¹ * |Rho5.CanonicalTail.delta M| := by
    rw [Rho5.ExternalThreePivot.thirdMagnitude, Rho5.ExternalThreePivot.lastMagnitude,
      if_neg hne, scaledS3_fixedSchur_fixedSchur M hk hr,
      Rho5.MatrixNormalization.smul_apply_entry, ← delta_eq_fixedSchur M,
      abs_mul, abs_inv, abs_of_pos hk]
  rw [hmain, div_eq_inv_mul]

/-! ## 3. `A3` 满足 D83 的输入结构 -/

/-- **阶段 A 的结构定理**：实际 `M` 在 `M 0 0 = 1` 与 `PolyCP M` 下，`A3 = (k M)⁻¹ • S3 M`
确实是 D83 外脑矩阵包络的合法输入。

用的是 D62 的 `polyCP_iff_frame` 反向读出的**实际 frame**：第三前导完整主元（条目界与
`|A3 0 0| = 1`）、第四前导完整主元（缩放后的 `fixedSchur (A3)` 资格），加上 `k, r > 0`。
**没有**假设尾部增长，**没有**要求五个主元全非零。 -/
theorem fixedOrderNormalized3_scaledS3 (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.ExternalThreePivot.FixedOrderNormalized3 (scaledS3 M) := by
  obtain ⟨_, _, _, hcpS3, hcpT2, _, hk, _⟩ :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact abs_scaledS3_le_one M hk hcpS3 i j
  · rw [scaledS3_zero_zero M (ne_of_gt hk), abs_one]
  · rw [scaledS3_fixedSchur M hk]
    exact (Rho5.MatrixNormalization.isCompletePivot_smul_iff (T2 M) 0 0
      (inv_ne_zero (ne_of_gt hk))).mpr hcpT2

/-! ## 4. 实际包络：复用 D83 的两条具名定理 -/

/-- **实际最后三阶包络（乘法形式）**：`|delta M| ≤ k M * phi (r M / k M)`。

把 D83 的 `fixed_order_three_pivot_envelope` 用在 `A3` 上，代入两个实际读数，再用
`k M > 0` 乘回。 -/
theorem delta_abs_le_k_mul_phi (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    |Rho5.CanonicalTail.delta M| ≤ k M * Rho5.ExternalThreePivot.phi (r M / k M) := by
  obtain ⟨_, _, _, _, _, _, hk, hr⟩ := (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  have hA := fixedOrderNormalized3_scaledS3 M h00 hCP
  have hEnv := (Rho5.ExternalThreePivot.fixed_order_three_pivot_envelope
    (scaledS3 M) hA).2.2
  rw [thirdMagnitude_scaledS3 M hk hr, secondMagnitude_scaledS3 M hk hr] at hEnv
  calc |Rho5.CanonicalTail.delta M|
      = |Rho5.CanonicalTail.delta M| / k M * k M :=
        (div_mul_cancel₀ _ (ne_of_gt hk)).symm
    _ ≤ Rho5.ExternalThreePivot.phi (r M / k M) * k M :=
        mul_le_mul_of_nonneg_right hEnv hk.le
    _ = k M * Rho5.ExternalThreePivot.phi (r M / k M) := mul_comm _ _

/-- **实际最后三阶包络（常数形式）**：`|delta M| ≤ (9 : ℝ) / 4 * k M`，即 D83 的锐界
`(9/4)` 直接落到实际 `delta` 上。 -/
theorem delta_abs_le_nine_quarters_mul_k (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M := by
  obtain ⟨_, _, _, _, _, _, hk, hr⟩ := (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  have hA := fixedOrderNormalized3_scaledS3 M h00 hCP
  have hEnv := Rho5.ExternalThreePivot.fixed_order_three_pivot_le_nine_quarters
    (scaledS3 M) hA
  rw [thirdMagnitude_scaledS3 M hk hr] at hEnv
  calc |Rho5.CanonicalTail.delta M|
      = |Rho5.CanonicalTail.delta M| / k M * k M :=
        (div_mul_cancel₀ _ (ne_of_gt hk)).symm
    _ ≤ (9 : ℝ) / 4 * k M := mul_le_mul_of_nonneg_right hEnv hk.le

/-- **阶段 A 入口定理**：把所有已验证内容打包给阶段 B 使用。 -/
theorem actual_last_three_envelope (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) :
    Rho5.ExternalThreePivot.FixedOrderNormalized3 (scaledS3 M) ∧
      Rho5.ExternalThreePivot.secondMagnitude (scaledS3 M) = r M / k M ∧
      Rho5.ExternalThreePivot.thirdMagnitude (scaledS3 M)
        = |Rho5.CanonicalTail.delta M| / k M ∧
      0 < k M ∧ 0 < r M ∧
      |Rho5.CanonicalTail.delta M| ≤ k M * Rho5.ExternalThreePivot.phi (r M / k M) ∧
      |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M := by
  obtain ⟨_, _, _, _, _, _, hk, hr⟩ := (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hCP
  exact ⟨fixedOrderNormalized3_scaledS3 M h00 hCP,
    secondMagnitude_scaledS3 M hk hr,
    thirdMagnitude_scaledS3 M hk hr,
    hk, hr,
    delta_abs_le_k_mul_phi M h00 hCP,
    delta_abs_le_nine_quarters_mul_k M h00 hCP⟩

/-! ## 5. 真实 `delta` 的三种符号都被同一条结论覆盖

这些推论**不引入**任何新假设：它们只是在同一条无条件绝对值界上取 `delta = 0`、
`delta < 0`、`0 < delta` 三个真实分支，用来表明卡上要求的三种情形都已覆盖，
而不是把 `delta ≠ 0` 当成前提。 -/

/-- `delta M` 的三个真实分支（实数三分律）。 -/
theorem delta_sign_trichotomy (M : Matrix5) :
    Rho5.CanonicalTail.delta M = 0 ∨ Rho5.CanonicalTail.delta M < 0
      ∨ 0 < Rho5.CanonicalTail.delta M := by
  rcases lt_trichotomy (Rho5.CanonicalTail.delta M) 0 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- `delta M = 0` 分支：末位读数确实为 `0`，而常数界仍是同一条。 -/
theorem envelope_delta_zero (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) (hdelta : Rho5.CanonicalTail.delta M = 0) :
    Rho5.ExternalThreePivot.thirdMagnitude (scaledS3 M) = 0 ∧
      |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M := by
  obtain ⟨_, _, hthird, _, _, _, h94⟩ := actual_last_three_envelope M h00 hCP
  exact ⟨by rw [hthird, hdelta]; simp, h94⟩

/-- `delta M < 0` 分支：绝对值就是 `-delta M`，界不变。 -/
theorem envelope_delta_neg (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) (hdelta : Rho5.CanonicalTail.delta M < 0) :
    |Rho5.CanonicalTail.delta M| = -Rho5.CanonicalTail.delta M ∧
      |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M := by
  obtain ⟨_, _, _, _, _, _, h94⟩ := actual_last_three_envelope M h00 hCP
  exact ⟨abs_of_neg hdelta, h94⟩

/-- `0 < delta M` 分支：绝对值就是 `delta M`，界不变。 -/
theorem envelope_delta_pos (M : Matrix5) (h00 : M 0 0 = 1)
    (hCP : Rho5.MinorCPDomain.PolyCP M) (hdelta : 0 < Rho5.CanonicalTail.delta M) :
    |Rho5.CanonicalTail.delta M| = Rho5.CanonicalTail.delta M ∧
      |Rho5.CanonicalTail.delta M| ≤ (9 : ℝ) / 4 * k M := by
  obtain ⟨_, _, _, _, _, _, h94⟩ := actual_last_three_envelope M h00 hCP
  exact ⟨abs_of_pos hdelta, h94⟩

end Rho5.LastThreePivotEnvelope
