/-
D63 — 用实际整矩阵转置给尾部非对角元排序
==========================================

1. **尾部坐标的转置关系**（复用 D36 已付的全路径转置）：对实际 `M` 与 `N = Mᵀ`，

   `S4 N = (S4 M)ᵀ`、`S3 N = (S3 M)ᵀ`、`T2 N = (T2 M)ᵀ`，且
   `p N = p M`、`k N = k M`、`r N = r M`、`T2 N 1 1 = T2 M 1 1`、
   `s N = t M`、`t N = s M`、`δ N = δ M`。

   D36 的 `pivotSchur_transpose` 是**全定义**等式（无分母/非零前提），故这些运输不需要
   任何平衡或非零假设；需要非零前提的地方一律沿用 D36 已付接口显式保留。
2. **排序**：`0 ≤ s M`、`0 ≤ t M` 时在 `M` 与 `Mᵀ` 中选一个实际矩阵 `P`，使
   `0 ≤ s P ≤ t P`，同时保持 `matrixEntryMax`、`M 0 0 = 1`、四层首位置 CP 资格、
   真实 `LegalTrace` 值表、增长比与全局比较（全部经 D36 的已付接口）。这是**整矩阵转置**，
   不是孤立尾块编辑。
3. **`4 < rho5Trace` 下的实际规范见证**：把 D53 的非负尾符号见证经上述排序，得到
   `0 ≤ s P ≤ t P`，并原样保留 D59 的第四主元支路与末主元严格分支（含 `s,t > 0`、
   `det P = -(p P*k P*r P*g) < 0`、`det P ≠ 0`）。`4 < rho5Trace` 仍是显式前提。
4. **与 D55 边界的兼容**：`shift Mᵀ h = (shift M h)ᵀ`；四个涉及的对角条目
   （`M 4 4`、`S4 M 3 3`、`S3 M 2 2`、`T2 M 1 1 = d M`）与 `p/k/r` 在转置下不变，
   故 `L Mᵀ = L M`、`U Mᵀ = U M`、`Feasible Mᵀ h ↔ Feasible M h`——D57 边界代表一旦提供，
   即可在其**之后**排序；本卡不依赖未完成的 D57，也不丢弃前三个面、不声明全局平衡。

**不声明**：`4 < rho5Trace` 本身、平衡尾、alpha 尖锐性、全局覆盖。
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Rho5.Shared.TraceTranspose
import Rho5.Shared.BottomRightVariation
import Rho5.Shared.DominantLastPivot

namespace Rho5.TailTransposeOrder

open scoped Matrix
open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. 尾部坐标的转置关系 -/

/-- **目标 1（`S4`）**：`S4 (Mᵀ) = (S4 M)ᵀ`（D36 全定义转置 + `S4` 定义）。 -/
theorem S4_transpose (M : Matrix5) : S4 Mᵀ = (S4 M)ᵀ := by
  rw [S4, S4, Rho5.TraceTranspose.pivotSchur_transpose]

/-- **目标 1（`S3`）**。 -/
theorem S3_transpose (M : Matrix5) : S3 Mᵀ = (S3 M)ᵀ := by
  rw [S3, S3, S4_transpose, Rho5.TraceTranspose.pivotSchur_transpose]

/-- **目标 1（`T2`）**。 -/
theorem T2_transpose (M : Matrix5) : T2 Mᵀ = (T2 M)ᵀ := by
  rw [T2, T2, S3_transpose, Rho5.TraceTranspose.pivotSchur_transpose]

/-- **目标 1（`p`）**：`p (Mᵀ) = p M`。 -/
theorem p_transpose (M : Matrix5) : p Mᵀ = p M := by
  simp [p, S4_transpose, Matrix.transpose_apply]

/-- **目标 1（`k`）**：`k (Mᵀ) = k M`。 -/
theorem k_transpose (M : Matrix5) : k Mᵀ = k M := by
  simp [k, S3_transpose, Matrix.transpose_apply]

/-- **目标 1（`r`）**：`r (Mᵀ) = r M`。 -/
theorem r_transpose (M : Matrix5) : r Mᵀ = r M := by
  simp [r, T2_transpose, Matrix.transpose_apply]

/-- **目标 1（`d = T2 · 1 1`）**：`d (Mᵀ) = d M`（对角条目）。 -/
theorem d_transpose (M : Matrix5) : T2 Mᵀ 1 1 = T2 M 1 1 := by
  simp [T2_transpose, Matrix.transpose_apply]

/-- **目标 1（非对角交换）**：`s (Mᵀ) = t M`。 -/
theorem s_transpose (M : Matrix5) : s Mᵀ = t M := by
  simp [s, t, T2_transpose, Matrix.transpose_apply]

/-- **目标 1（非对角交换）**：`t (Mᵀ) = s M`。 -/
theorem t_transpose (M : Matrix5) : t Mᵀ = s M := by
  simp [t, s, T2_transpose, Matrix.transpose_apply]

/-- **目标 1（`δ` 不变）**：`δ (Mᵀ) = δ M`（`d` 不变、`s`/`t` 交换，商 `t*s/r` 对称）。 -/
theorem delta_transpose (M : Matrix5) : Rho5.CanonicalTail.delta Mᵀ = Rho5.CanonicalTail.delta M := by
  simp only [Rho5.CanonicalTail.delta, d_transpose, s_transpose, t_transpose, r_transpose,
    mul_comm]

/-- **目标 1（CP 资格经转置保留）**：D36 的 `(0,0)` 完整主元转置等价，用在四层上。 -/
theorem isCompletePivot_transpose (M : Matrix5) :
    (Rho5.Pivot.IsCompletePivot Mᵀ 0 0 ↔ Rho5.Pivot.IsCompletePivot M 0 0) ∧
      (Rho5.Pivot.IsCompletePivot (S4 Mᵀ) 0 0 ↔ Rho5.Pivot.IsCompletePivot (S4 M) 0 0) ∧
        (Rho5.Pivot.IsCompletePivot (S3 Mᵀ) 0 0 ↔ Rho5.Pivot.IsCompletePivot (S3 M) 0 0) ∧
          (Rho5.Pivot.IsCompletePivot (T2 Mᵀ) 0 0 ↔
            Rho5.Pivot.IsCompletePivot (T2 M) 0 0) := by
  refine ⟨(Rho5.TraceTranspose.isCompletePivot_transpose_iff M 0 0).symm, ?_, ?_, ?_⟩
  · rw [S4_transpose]
    exact (Rho5.TraceTranspose.isCompletePivot_transpose_iff (S4 M) 0 0).symm
  · rw [S3_transpose]
    exact (Rho5.TraceTranspose.isCompletePivot_transpose_iff (S3 M) 0 0).symm
  · rw [T2_transpose]
    exact (Rho5.TraceTranspose.isCompletePivot_transpose_iff (T2 M) 0 0).symm

/-- **目标 1（D36 已付保持包）**：归一化、`0 0`、真实迹值表、增长比在转置下不变。 -/
theorem transpose_preserves (M : Matrix5) (values : List ℝ) :
    matrixEntryMax Mᵀ = matrixEntryMax M ∧ Mᵀ 0 0 = M 0 0 ∧
      (Rho5.CompletePivotPath.LegalTrace Mᵀ values ↔
        Rho5.CompletePivotPath.LegalTrace M values) ∧
        Rho5.GrowthModel.growthRatio Mᵀ values = Rho5.GrowthModel.growthRatio M values :=
  ⟨Rho5.TraceTranspose.matrixEntryMax_transpose M, Rho5.TraceTranspose.transpose_zero_zero M,
    Rho5.TraceTranspose.legalTrace_transpose_iff,
    Rho5.TraceTranspose.growthRatio_transpose M values⟩

/-! ## 2. 用整矩阵转置排序 `0 ≤ s ≤ t` -/

/-- **目标 2（选择）**：`0 ≤ s M`、`0 ≤ t M` 时，`M` 或 `Mᵀ` 中至少一个满足 `0 ≤ s ≤ t`
（`s (Mᵀ) = t M`、`t (Mᵀ) = s M`，故两者必取其序）。 -/
theorem ordered_or_transpose_ordered (M : Matrix5) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    (0 ≤ s M ∧ s M ≤ t M) ∨ (0 ≤ s Mᵀ ∧ s Mᵀ ≤ t Mᵀ) := by
  rcases le_total (s M) (t M) with h | h
  · exact Or.inl ⟨hs, h⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [s_transpose]; exact ht
    · rw [s_transpose, t_transpose]; exact h

/-- **目标 2（实际矩阵见证）**：给定 `0 ≤ s M`、`0 ≤ t M` 与 D48/D53 已付的规范资格
（归一化、`M 0 0 = 1`、四层 CP、真实迹值表），存在**实际矩阵** `P`（等于 `M` 或 `Mᵀ`）
使 `0 ≤ s P ≤ t P`，且上述资格与增长比全部保持。 -/
theorem exists_ordered_tail_matrix (M : Matrix5) (values : List ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp0 : Rho5.Pivot.IsCompletePivot M 0 0)
    (hcp4 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0)
    (hcp2 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (htrace : Rho5.CompletePivotPath.LegalTrace M values) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    ∃ P : Matrix5,
      (P = M ∨ P = Mᵀ) ∧ matrixEntryMax P = 1 ∧ P 0 0 = 1 ∧
        Rho5.Pivot.IsCompletePivot P 0 0 ∧ Rho5.Pivot.IsCompletePivot (S4 P) 0 0 ∧
          Rho5.Pivot.IsCompletePivot (S3 P) 0 0 ∧
            Rho5.Pivot.IsCompletePivot (T2 P) 0 0 ∧
              Rho5.CompletePivotPath.LegalTrace P values ∧ 0 ≤ s P ∧ s P ≤ t P ∧
                Rho5.GrowthModel.growthRatio P values =
                  Rho5.GrowthModel.growthRatio M values := by
  rcases ordered_or_transpose_ordered M hs ht with ⟨hs', hst⟩ | ⟨hs', hst⟩
  · exact ⟨M, Or.inl rfl, hmax, h00, hcp0, hcp4, hcp3, hcp2, htrace, hs', hst, rfl⟩
  · refine ⟨Mᵀ, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs', hst, ?_⟩
    · rw [Rho5.TraceTranspose.matrixEntryMax_transpose]; exact hmax
    · rw [Rho5.TraceTranspose.transpose_zero_zero]; exact h00
    · exact (isCompletePivot_transpose M).1.mpr hcp0
    · exact (isCompletePivot_transpose M).2.1.mpr hcp4
    · exact (isCompletePivot_transpose M).2.2.1.mpr hcp3
    · exact (isCompletePivot_transpose M).2.2.2.mpr hcp2
    · exact Rho5.TraceTranspose.legalTrace_transpose_iff.mpr htrace
    · rw [Rho5.TraceTranspose.growthRatio_transpose]

/-! ## 3. `4 < rho5Trace` 下排序后的实际规范见证（保留 D59 二分） -/

/-- **目标 2/3（规范见证 + 排序 + D59 二分）**：`4 < rho5Trace` 下，存在实际矩阵 `P`
（D53/D59 规范见证 `N = signedEntries M (sigma5 ε) (sigma5 η)` 的 `N` 或 `Nᵀ`），满足
`0 ≤ s P ≤ t P`、归一化、真实迹值表与全局比较，并且 D59 的二分原样保留：第四主元支路
`g = r P ∧ 4 < r P`，或末主元严格分支（`s P, t P > 0`、`δ P = -g`、
`det P = -(p P*k P*r P*g) < 0`、`det P ≠ 0`）。**`P` 的 D53 出处写在结论里**，
故这是实际整矩阵（符号规范的整矩阵像或其转置），不是孤立尾块编辑。 -/
theorem exists_ordered_canonical_witness (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N P : Matrix5) (ε η : ℝ) (values : List ℝ) (g : ℝ),
      N = Rho5.TraceSigns.signedEntries M (Rho5.TailSignNormalization.sigma5 ε)
            (Rho5.TailSignNormalization.sigma5 η) ∧
        (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧ (P = N ∨ P = Nᵀ) ∧
      matrixEntryMax P = 1 ∧ P ≠ 0 ∧ P 0 0 = 1 ∧
        Rho5.CompletePivotPath.LegalTrace P values ∧
          values = [1, p P, k P, r P, |Rho5.CanonicalTail.delta P|] ∧
            0 ≤ s P ∧ s P ≤ t P ∧
              g = Rho5.GrowthModel.growthRatio P values ∧
                g = Rho5.GrowthSupremum.rho5Trace ∧
                  (∀ (P' : Matrix5), P' ≠ 0 → ∀ ws : List ℝ,
                    Rho5.CompletePivotPath.LegalTrace P' ws →
                      Rho5.GrowthModel.growthRatio P' ws ≤ g) ∧
                    ( (g = r P ∧ 4 < r P) ∨
                      (r P < g ∧ Rho5.CanonicalTail.delta P = -g ∧ 0 < s P ∧ 0 < t P ∧
                        P.det = -(p P * k P * r P * g) ∧ P.det < 0 ∧ P.det ≠ 0) ) := by
  obtain ⟨M, N, ε, η, values, g, hN, hε, hη, _hM, _hMne, _h00, _hpos, _hcp0, _hcp4, _hcp3,
    _hcp2, _hp, _hk, _hr, _hvalues, _hratio, hmaxN, hNne, hN00, _hpN, _hkN, _hrN, hsN, htN,
    htraceN, hvaluesN, hg, hgrho, hcmp, halt⟩ :=
    Rho5.DominantLastPivot.exists_global_maximizer_alternative h4
  rcases le_total (s N) (t N) with hle | hle
  · exact ⟨M, N, N, ε, η, values, g, hN, hε, hη, Or.inl rfl, hmaxN, hNne, hN00, htraceN, hvaluesN,
      hsN, hle, hg, hgrho, hcmp, halt⟩
  · refine ⟨M, N, Nᵀ, ε, η, values, g, hN, hε, hη, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [Rho5.TraceTranspose.matrixEntryMax_transpose]; exact hmaxN
    · rwa [Rho5.TraceTranspose.transpose_ne_zero_iff]
    · rw [Rho5.TraceTranspose.transpose_zero_zero]; exact hN00
    · exact Rho5.TraceTranspose.legalTrace_transpose_iff.mpr htraceN
    · rw [delta_transpose, p_transpose, k_transpose, r_transpose]; exact hvaluesN
    · rw [s_transpose]; exact htN
    · rw [s_transpose, t_transpose]; exact hle
    · rw [Rho5.TraceTranspose.growthRatio_transpose]; exact hg
    · exact hgrho
    · intro P' hP' ws hws
      exact hcmp P' hP' ws hws
    · rcases halt with ⟨h1, h2⟩ | h3
      · left
        exact ⟨by rw [r_transpose]; exact h1, by rw [r_transpose]; exact h2⟩
      · right
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h3
        have hdetT : Nᵀ.det = N.det := Matrix.det_transpose N
        refine ⟨by rw [r_transpose]; exact h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [delta_transpose]; exact h2
        · rw [s_transpose]; exact h4
        · rw [t_transpose]; exact h3
        · rw [hdetT, h5, p_transpose, k_transpose, r_transpose]
        · rw [hdetT]; exact h6
        · rw [hdetT]; exact h7

/-! ## 4. 与 D55 边界的兼容 -/

/-- **目标 4（`shift` 与转置交换）**：`shift (Mᵀ) h = (shift M h)ᵀ`——`shift` 只动 `(4,4)`
一个条目，转置把 `(4,4)` 映到自身。 -/
theorem shift_transpose (M : Matrix5) (h : ℝ) :
    Rho5.BottomRightVariation.shift Mᵀ h = (Rho5.BottomRightVariation.shift M h)ᵀ := by
  ext i j
  by_cases hij : i = 4 ∧ j = 4
  · have hji : j = 4 ∧ i = 4 := ⟨hij.2, hij.1⟩
    simp only [Rho5.BottomRightVariation.shift_apply, Matrix.transpose_apply]
    rw [if_pos hij, if_pos hji]
  · have hji : ¬(j = 4 ∧ i = 4) := fun h' => hij ⟨h'.2, h'.1⟩
    simp only [Rho5.BottomRightVariation.shift_apply, Matrix.transpose_apply]
    rw [if_neg hij, if_neg hji]

/-- **目标 4（四个涉及对角条目 + `p/k/r` 不变）**。 -/
theorem diag_transpose (M : Matrix5) :
    Mᵀ 4 4 = M 4 4 ∧ S4 Mᵀ 3 3 = S4 M 3 3 ∧ S3 Mᵀ 2 2 = S3 M 2 2 ∧
      Rho5.BottomRightVariation.d Mᵀ = Rho5.BottomRightVariation.d M ∧
        p Mᵀ = p M ∧ k Mᵀ = k M ∧ r Mᵀ = r M :=
  ⟨rfl, by rw [S4_transpose]; rfl, by rw [S3_transpose]; rfl,
    by rw [Rho5.BottomRightVariation.d, Rho5.BottomRightVariation.d]; exact d_transpose M,
    p_transpose M, k_transpose M, r_transpose M⟩

/-- **目标 4（下端点不变）**：`L (Mᵀ) = L M`。 -/
theorem L_transpose (M : Matrix5) :
    Rho5.BottomRightVariation.L Mᵀ = Rho5.BottomRightVariation.L M := by
  rw [Rho5.BottomRightVariation.L, Rho5.BottomRightVariation.L]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := diag_transpose M
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- **目标 4（上端点不变）**：`U (Mᵀ) = U M`。 -/
theorem U_transpose (M : Matrix5) :
    Rho5.BottomRightVariation.U Mᵀ = Rho5.BottomRightVariation.U M := by
  rw [Rho5.BottomRightVariation.U, Rho5.BottomRightVariation.U]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := diag_transpose M
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- **目标 4（四条实际条目约束不变）**：`Feasible (Mᵀ) h ↔ Feasible M h`，
故 `L` 处的四路饱和选择在转置下逐个保持。 -/
theorem feasible_transpose_iff (M : Matrix5) (h : ℝ) :
    Rho5.BottomRightVariation.Feasible Mᵀ h ↔ Rho5.BottomRightVariation.Feasible M h := by
  rw [Rho5.BottomRightVariation.Feasible, Rho5.BottomRightVariation.Feasible]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := diag_transpose M
  simp only [h1, h2, h3, h4, h5, h6, h7]

end Rho5.TailTransposeOrder
