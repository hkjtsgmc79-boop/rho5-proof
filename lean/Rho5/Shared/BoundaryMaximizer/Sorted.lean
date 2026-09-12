/-
D68 阶段 A — **实际存在的排序四边界最大者**
==============================================

在显式前提 `4 < rho5Trace` 下：

1. 取 D57 阶段 B 的**实际**四边界最大者
   `S = shift N (L N)`（`N = signedEntries M (sigma5 ε) (sigma5 η)`），它仍达到
   `rho5Trace`、带真实 `LegalTrace`/四层 CP/`p,k,r > 0`/`0 ≤ s, t`，并落在四选一饱和边界上；
2. 用 D63 的**整矩阵转置选择** `exists_ordered_tail_matrix` 在 `{S, Sᵀ}` 中选出实际矩阵 `P`，
   使 `0 ≤ s P ≤ t P`（转置把 `(s,t)` 换成 `(t,s)`，故两者必取其序）；
3. 把 `P` 的五阶固定事实装进 `SortedBoundaryMaximizerFacts`：归一化 `P 0 0 = 1`、
   四层 CP、`p/k/r > 0`、真实迹值表 `values = [1, p P, k P, r P, |δ P|]`、
   真实 `LegalTrace`、`growthRatio P values = rho5Trace`、**四个饱和面全保留**，
   以及**原全矩阵/全迹比较**。

`P = S` 分支直接取 D57 事实；`P = Sᵀ` 分支用 `BoundaryMaximizerCore.transpose`
（四个面都是对角条目，故一个不少）。**没有**交换任何部分尾部操作、**没有**重跑 D55。

**不声称**：`4 < rho5Trace`（仍是显式前提）、满秩、`d = -r`、全域可平衡、
`rho5 = alpha`、最大值的唯一性，也不把四分支收敛为"仅平衡尾"。
-/
import Rho5.Shared.BoundaryMaximizer.Core
import Rho5.Shared.TailBoundaryReduction.Witness

namespace Rho5.BoundaryMaximizer

open scoped Matrix
open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D68 阶段 A 主定理（实际存在性）**：`4 < rho5Trace` 下存在实际矩阵 `M`、其符号化
整矩阵 `N`（`N = signedEntries M (sigma5 ε) (sigma5 η)`，`ε, η = ±1`）、实际矩阵
`P`（`P = shift N (L N)` 或其**整矩阵转置**）与真实迹值表 `values`，使 `P` 满足
`SortedBoundaryMaximizerFacts`：`0 ≤ s P ≤ t P`、归一化、四层 CP、`p/k/r > 0`、
真实 `LegalTrace` 与迹值表、增长比恰为 `rho5Trace`、四选一饱和边界**四个面全保留**、
且仍是原全矩阵/全迹比较下的最大者。 -/
theorem exists_sorted_boundary_maximizer (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N P : Matrix5) (ε η : ℝ) (values : List ℝ),
      N = Rho5.TraceSigns.signedEntries M (Rho5.TailSignNormalization.sigma5 ε)
            (Rho5.TailSignNormalization.sigma5 η) ∧
        (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
          (P = Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N) ∨
            P = (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))ᵀ) ∧
            SortedBoundaryMaximizerFacts P values := by
  -- D57 阶段 B：实际四边界最大者 `S = shift N (L N)`
  obtain ⟨M, N, ε, η, values, hmaxM, hMne, h00M, hposM, hcp0M, hcp4M, hcp3M, hcp2M, hpM, hkM,
    hrM, hvaluesM, hratioM, hε, hη, hNM, hmaxN, h00N, hsN, htN, htraceN, hratioN, hmaxS, h00S,
    hcp0S, hcp4S, hcp3S, hcp2S, hpS, hkS, hrS, hsS, htS, htraceS, hrhoS, hpeakS, hbranchS, hbdS,
    hcmpS⟩ := Rho5.TailBoundaryReduction.exists_boundary_maximizer h4
  -- D63：整矩阵转置选择，得到 `0 ≤ s ≤ t` 的实际矩阵 `P ∈ {S, Sᵀ}`
  obtain ⟨P, hPS, hmaxP, h00P, hcp0P, hcp4P, hcp3P, hcp2P, htraceP, hsP, hstP, hratioPS⟩ :=
    Rho5.TailTransposeOrder.exists_ordered_tail_matrix
      (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
      (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N))
      hmaxS h00S hcp0S hcp4S hcp3S hcp2S htraceS hsS htS
  -- `S ≠ 0`（由 `S 0 0 = 1`）
  have hneS : Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N) ≠ 0 := by
    intro h0
    have h01 : (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) 0 0 = 0 := by
      rw [h0]
      simp
    have h10 : (0 : ℝ) = 1 := by
      rw [← h01]
      exact h00S
    exact zero_ne_one h10
  -- `S` 的核心事实包（值表用 `traceValues_shift_eq` 换成 `S` 自身的读数）
  have hcoreS : BoundaryMaximizerCore
      (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
      (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) :=
    { ne_zero := hneS,
      entryMax := hmaxS,
      zero_zero := h00S,
      cp0 := hcp0S,
      cp4 := hcp4S,
      cp3 := hcp3S,
      cp2 := hcp2S,
      p_pos := hpS,
      k_pos := hkS,
      r_pos := hrS,
      trace_eq := traceValues_shift_eq N (Rho5.BottomRightVariation.L N),
      legal := htraceS,
      growth_eq_rho := hrhoS,
      boundary := hbdS,
      global_max := hcmpS }
  -- 核心包搬到实际矩阵 `P`（`P = S` 直接取，`P = Sᵀ` 走转置不变性）
  have hcoreP : BoundaryMaximizerCore P
      (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) := by
    rcases hPS with hPSl | hPSt
    · rw [hPSl]
      exact hcoreS
    · rw [hPSt]
      exact hcoreS.transpose
  -- 增长比仍为 `rho5Trace`（D63 保持增长比）
  have hgrowthP : Rho5.GrowthModel.growthRatio P
      (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) =
        Rho5.GrowthSupremum.rho5Trace := by
    rw [hratioPS]
    exact hrhoS
  -- 原全矩阵/全迹比较照搬（右端即 `P` 的增长比）
  have hglobalP : ∀ (M' : Matrix5), M' ≠ 0 → ∀ ws : List ℝ,
      Rho5.CompletePivotPath.LegalTrace M' ws →
        Rho5.GrowthModel.growthRatio M' ws ≤
          Rho5.GrowthModel.growthRatio P
            (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) := by
    intro M' hM' ws hws
    rw [hratioPS]
    exact hcmpS M' hM' ws hws
  exact ⟨M, N, P, ε, η, Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N),
    hNM, hε, hη, hPS,
    { toBoundaryMaximizerCore :=
        { hcoreP with growth_eq_rho := hgrowthP, global_max := hglobalP },
      s_nonneg := hsP,
      s_le_t := hstP }⟩

/-- **四边界 + 排序的紧凑形式**（下游按支路消费用）：存在实际矩阵 `P` 与真实迹值表，
`0 ≤ s P ≤ t P`，且**四个饱和面一个不少**。 -/
theorem exists_sorted_boundary_maximizer_four_faces (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (P : Matrix5) (values : List ℝ),
      SortedBoundaryMaximizerFacts P values ∧ 0 ≤ s P ∧ s P ≤ t P ∧
        (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨ T2 P 1 1 = -r P) := by
  obtain ⟨M, N, P, ε, η, values, -, -, -, -, h⟩ := exists_sorted_boundary_maximizer h4
  exact ⟨P, values, h, h.s_nonneg, h.s_le_t, h.boundary⟩

end Rho5.BoundaryMaximizer
