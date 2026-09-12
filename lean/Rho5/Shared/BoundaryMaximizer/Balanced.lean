/-
D68 阶段 B — 第四支路上的**显式平衡物理见证**（消费 D65 FRAME_READY）
=========================================================================

阶段 A 已给出实际排序四边界最大者 `P` 与**四个**饱和面。本文件只在**第四支路**
`T2 P 1 1 = -r P` 上消费 D65 的已验收 frame 版本
（`Rho5.Certificate.BalancedMaximizer.frame_physical_point_at_height`，
冻结回执 sha `62bcf3cb…`），得到**显式** B24 点 `extract P`
（`Rho5.Certificate.B16.Point = Fin 24 → ℝ`，原 B24 坐标类型，不是矩阵）：
`Physical (extract P)`、`HeadBand (extract P)`、`(extract P) 23 = rho5Trace`、
`reconstruct (extract P) = P`。

返回的是**完整析取**：前三个边界面（`P 4 4 = -1`、`S4 P 3 3 = -p P`、`S3 P 2 2 = -k P`）
**原样保留**，第四支路才附上平衡物理见证。

**不声称**：`4 < rho5Trace`（仍是显式前提）、全域可平衡、任何矩阵都存在平衡支、
`rho5Trace = alpha`、最大值可达、G04 见证降低；**不**把四个面收敛为一个。
-/
import Rho5.Shared.BoundaryMaximizer.Sorted
import Rho5.Certificate.BalancedMaximizer.Frame

namespace Rho5.BoundaryMaximizer

open scoped Matrix
open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D68 阶段 B 主定理（完整析取）**：`4 < rho5Trace` 下存在阶段 A 的实际排序四边界最大者
`P`（`P = shift N (L N)` 或其整矩阵转置，`N = signedEntries M (sigma5 ε) (sigma5 η)`），
使下列**四选一**成立且**四个面一个不少**：

* `P 4 4 = -1`，或 `S4 P 3 3 = -p P`，或 `S3 P 2 2 = -k P`；**或**
* 第四支路 `T2 P 1 1 = -r P`，并附上**显式** B24 点 `z = extract P`（`z : B16.Point`）：
  `Physical z`、`HeadBand z`、`z 23 = rho5Trace`、`reconstruct z = P`。

平衡见证**只在这条支路上**出现；本定理既不丢弃前三个面，也不声称全域可平衡。 -/
theorem exists_sorted_boundary_maximizer_faces_or_balanced
    (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N P : Matrix5) (ε η : ℝ) (values : List ℝ),
      N = Rho5.TraceSigns.signedEntries M (Rho5.TailSignNormalization.sigma5 ε)
            (Rho5.TailSignNormalization.sigma5 η) ∧
        (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
          (P = Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N) ∨
            P = (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))ᵀ) ∧
            SortedBoundaryMaximizerFacts P values ∧
              (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨
                (T2 P 1 1 = -r P ∧
                  ∃ z : Rho5.Certificate.B16.Point, z = Rho5.Certificate.B24Extraction.extract P ∧
                    Rho5.Certificate.B16.Physical z ∧
                      Rho5.Certificate.B24Reconstruction.HeadBand z ∧
                        z 23 = Rho5.GrowthSupremum.rho5Trace ∧
                          Rho5.Certificate.B24Reconstruction.reconstruct z = P)) := by
  obtain ⟨M, N, P, ε, η, values, hNM, hε, hη, hPS, hfacts⟩ :=
    exists_sorted_boundary_maximizer h4
  -- `values` 就是 D65 frame 使用的 `balancedValues P`（同一个五值表）
  have hbv : values = Rho5.Certificate.BalancedMaximizer.balancedValues P := by
    rw [hfacts.trace_eq]
    simp only [Rho5.Certificate.BalancedMaximizer.balancedValues]
  have hgrowthP : 4 < Rho5.GrowthModel.growthRatio P
      (Rho5.Certificate.BalancedMaximizer.balancedValues P) := by
    rw [← hbv, hfacts.growth_eq_rho]
    exact h4
  have hrhoP : Rho5.GrowthModel.growthRatio P
      (Rho5.Certificate.BalancedMaximizer.balancedValues P) =
        Rho5.GrowthSupremum.rho5Trace := by
    rw [← hbv]
    exact hfacts.growth_eq_rho
  have ht_nonneg : 0 ≤ t P := le_trans hfacts.s_nonneg hfacts.s_le_t
  refine ⟨M, N, P, ε, η, values, hNM, hε, hη, hPS, hfacts, ?_⟩
  rcases hfacts.boundary with h1 | h2 | h3 | htail
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · refine Or.inr (Or.inr (Or.inr ⟨htail, ?_⟩))
    -- D65 frame（item 3）：显式点 `extract P` 的物理/头带/重构/高度
    obtain ⟨hPhys, hBand, hRec, h23, -⟩ :=
      Rho5.Certificate.BalancedMaximizer.frame_physical_point_at_height P
        hfacts.entryMax hfacts.zero_zero hfacts.cp0 hfacts.cp4 hfacts.cp3 hfacts.cp2
        hfacts.p_pos hfacts.k_pos hfacts.r_pos hgrowthP htail hfacts.s_nonneg ht_nonneg
    exact ⟨Rho5.Certificate.B24Extraction.extract P, rfl, hPhys, hBand,
      by rw [h23, hrhoP], hRec⟩

/-- **同一析取的紧凑形式**（只暴露三个面名 + 第四支路上 `extract P` 的显式见证）。 -/
theorem exists_sorted_boundary_maximizer_faces_or_balanced_compact
    (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (P : Matrix5) (values : List ℝ),
      SortedBoundaryMaximizerFacts P values ∧
        (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨
          (T2 P 1 1 = -r P ∧
            Rho5.Certificate.B16.Physical (Rho5.Certificate.B24Extraction.extract P) ∧
              Rho5.Certificate.B24Reconstruction.HeadBand (Rho5.Certificate.B24Extraction.extract P) ∧
                (Rho5.Certificate.B24Extraction.extract P) 23 = Rho5.GrowthSupremum.rho5Trace ∧
                  Rho5.Certificate.B24Reconstruction.reconstruct
                    (Rho5.Certificate.B24Extraction.extract P) = P)) := by
  obtain ⟨M, N, P, ε, η, values, hNM, hε, hη, hPS, hfacts⟩ :=
    exists_sorted_boundary_maximizer h4
  have hbv : values = Rho5.Certificate.BalancedMaximizer.balancedValues P := by
    rw [hfacts.trace_eq]
    simp only [Rho5.Certificate.BalancedMaximizer.balancedValues]
  have hgrowthP : 4 < Rho5.GrowthModel.growthRatio P
      (Rho5.Certificate.BalancedMaximizer.balancedValues P) := by
    rw [← hbv, hfacts.growth_eq_rho]
    exact h4
  have hrhoP : Rho5.GrowthModel.growthRatio P
      (Rho5.Certificate.BalancedMaximizer.balancedValues P) =
        Rho5.GrowthSupremum.rho5Trace := by
    rw [← hbv]
    exact hfacts.growth_eq_rho
  have ht_nonneg : 0 ≤ t P := le_trans hfacts.s_nonneg hfacts.s_le_t
  have hframe := Rho5.Certificate.BalancedMaximizer.frame_physical_point_at_height P
    hfacts.entryMax hfacts.zero_zero hfacts.cp0 hfacts.cp4 hfacts.cp3 hfacts.cp2
    hfacts.p_pos hfacts.k_pos hfacts.r_pos hgrowthP
  refine ⟨P, values, hfacts, ?_⟩
  rcases hfacts.boundary with h1 | h2 | h3 | htail
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · refine Or.inr (Or.inr (Or.inr ⟨htail, ?_, ?_, ?_, ?_⟩))
    · exact (hframe htail hfacts.s_nonneg ht_nonneg).1
    · exact (hframe htail hfacts.s_nonneg ht_nonneg).2.1
    · rw [(hframe htail hfacts.s_nonneg ht_nonneg).2.2.2.1, hrhoP]
    · exact (hframe htail hfacts.s_nonneg ht_nonneg).2.2.1

end Rho5.BoundaryMaximizer
