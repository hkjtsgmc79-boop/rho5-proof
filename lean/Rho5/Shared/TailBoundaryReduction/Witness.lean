/-
D57 阶段 B — 条件式真实四边界最大者（消费 D55 已验接口）
=============================================================

从 D53 的 `exists_canonical_tail_witness_nonneg`（前提 `4 < rho5Trace`）取出**符号化规范最大
矩阵** `N`（`s N ≥ 0`、`t N ≥ 0`，并由 D53 的已付运输带上四层 CP 与 `p/k/r > 0`），
再用 `StageB.shift_L_qualifications` 在 D55 的可行区间左端组装整矩阵 `shift N (L N)`：

* 它仍是**实际全局最大者**（增长比恰为 `rho5Trace`，原全局比较照搬）；
* 带真实 `LegalTrace`、四层 CP、归一化与 `s,t ≥ 0` 全部保持；
* 满足**四选一饱和边界**（四个面都保留）：
  `shift N (L N) 4 4 = -1 ∨ S4 (…) 3 3 = -p (…) ∨ S3 (…) 2 2 = -k (…) ∨ T2 (…) 1 1 = -r (…)`。

**不声称**：`4 < rho5Trace`（仍是假设）、满秩、`d = -r`、全域可平衡、`rho5 = alpha`；
**不**把四分支收敛为"仅平衡尾"。
-/
import Rho5.Shared.TailBoundaryReduction.StageB
import Rho5.Shared.TailSignNormalization

namespace Rho5.TailBoundaryReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D57 阶段 B 主定理**：在显式前提 `4 < rho5Trace` 下，存在真实 `M`（D48/D53 的规范最大
见证）、其符号化整矩阵 `N`（`s, t ≥ 0`）与左端位移矩阵 `shift N (L N)`，使后者仍达到
`rho5Trace`、保留全部资格与实际迹，并落在四选一饱和边界上。 -/
theorem exists_boundary_maximizer (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N : Matrix5) (ε η : ℝ) (values : List ℝ),
      matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 = 1 ∧
        Rho5.LeadingSigns.LeadingTracePos M values ∧
          Rho5.Pivot.IsCompletePivot M 0 0 ∧ Rho5.Pivot.IsCompletePivot (S4 M) 0 0 ∧
            Rho5.Pivot.IsCompletePivot (S3 M) 0 0 ∧ Rho5.Pivot.IsCompletePivot (T2 M) 0 0 ∧
              0 < p M ∧ 0 < k M ∧ 0 < r M ∧
                values = [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ∧
                  Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
                    (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
                      N = Rho5.TraceSigns.signedEntries M
                        (Rho5.TailSignNormalization.sigma5 ε)
                        (Rho5.TailSignNormalization.sigma5 η) ∧
                        matrixEntryMax N = 1 ∧ N 0 0 = 1 ∧ 0 ≤ s N ∧ 0 ≤ t N ∧
                          Rho5.CompletePivotPath.LegalTrace N values ∧
                            Rho5.GrowthModel.growthRatio N values =
                              Rho5.GrowthSupremum.rho5Trace ∧
                              matrixEntryMax
                                  (Rho5.BottomRightVariation.shift N
                                    (Rho5.BottomRightVariation.L N)) = 1 ∧
                                Rho5.BottomRightVariation.shift N
                                    (Rho5.BottomRightVariation.L N) 0 0 = 1 ∧
                                  Rho5.Pivot.IsCompletePivot
                                      (Rho5.BottomRightVariation.shift N
                                        (Rho5.BottomRightVariation.L N)) 0 0 ∧
                                    Rho5.Pivot.IsCompletePivot
                                        (S4 (Rho5.BottomRightVariation.shift N
                                          (Rho5.BottomRightVariation.L N))) 0 0 ∧
                                      Rho5.Pivot.IsCompletePivot
                                          (S3 (Rho5.BottomRightVariation.shift N
                                            (Rho5.BottomRightVariation.L N))) 0 0 ∧
                                        Rho5.Pivot.IsCompletePivot
                                            (T2 (Rho5.BottomRightVariation.shift N
                                              (Rho5.BottomRightVariation.L N))) 0 0 ∧
                                          0 < p (Rho5.BottomRightVariation.shift N
                                                (Rho5.BottomRightVariation.L N)) ∧
                                            0 < k (Rho5.BottomRightVariation.shift N
                                                  (Rho5.BottomRightVariation.L N)) ∧
                                              0 < r (Rho5.BottomRightVariation.shift N
                                                    (Rho5.BottomRightVariation.L N)) ∧
                                                0 ≤ s (Rho5.BottomRightVariation.shift N
                                                      (Rho5.BottomRightVariation.L N)) ∧
                                                  0 ≤ t (Rho5.BottomRightVariation.shift N
                                                        (Rho5.BottomRightVariation.L N)) ∧
                                                    Rho5.CompletePivotPath.LegalTrace
                                                      (Rho5.BottomRightVariation.shift N
                                                        (Rho5.BottomRightVariation.L N))
                                                      (Rho5.BottomRightVariation.traceValues N
                                                        (Rho5.BottomRightVariation.L N)) ∧
                                                      Rho5.GrowthModel.growthRatio
                                                        (Rho5.BottomRightVariation.shift N
                                                          (Rho5.BottomRightVariation.L N))
                                                        (Rho5.BottomRightVariation.traceValues N
                                                          (Rho5.BottomRightVariation.L N)) =
                                                        Rho5.GrowthSupremum.rho5Trace ∧
                                                        Rho5.GrowthModel.growthRatio
                                                          (Rho5.BottomRightVariation.shift N
                                                            (Rho5.BottomRightVariation.L N))
                                                          (Rho5.BottomRightVariation.traceValues N
                                                            (Rho5.BottomRightVariation.L N)) =
                                                          Rho5.GrowthModel.tracePeak
                                                            (Rho5.BottomRightVariation.traceValues N
                                                              (Rho5.BottomRightVariation.L N)) ∧
                                                          (Rho5.GrowthModel.growthRatio
                                                              (Rho5.BottomRightVariation.shift N
                                                                (Rho5.BottomRightVariation.L N))
                                                              (Rho5.BottomRightVariation.traceValues N
                                                                (Rho5.BottomRightVariation.L N)) =
                                                            r (Rho5.BottomRightVariation.shift N
                                                                (Rho5.BottomRightVariation.L N)) ∨
                                                            Rho5.GrowthModel.growthRatio
                                                              (Rho5.BottomRightVariation.shift N
                                                                (Rho5.BottomRightVariation.L N))
                                                              (Rho5.BottomRightVariation.traceValues N
                                                                (Rho5.BottomRightVariation.L N)) =
                                                              |Rho5.CanonicalTail.delta
                                                                (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N))|) ∧
                                                            (Rho5.BottomRightVariation.shift N
                                                                (Rho5.BottomRightVariation.L N) 4 4 = -1 ∨
                                                              S4 (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N)) 3 3 =
                                                                -p (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N)) ∨
                                                              S3 (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N)) 2 2 =
                                                                -k (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N)) ∨
                                                              T2 (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N)) 1 1 =
                                                                -r (Rho5.BottomRightVariation.shift N
                                                                  (Rho5.BottomRightVariation.L N))) ∧
                                                              ∀ (M' : Matrix5), M' ≠ 0 → ∀ ws : List ℝ,
                                                                Rho5.CompletePivotPath.LegalTrace M' ws →
                                                                  Rho5.GrowthModel.growthRatio M' ws ≤
                                                                    Rho5.GrowthModel.growthRatio
                                                                      (Rho5.BottomRightVariation.shift N
                                                                        (Rho5.BottomRightVariation.L N))
                                                                      (Rho5.BottomRightVariation.traceValues N
                                                                        (Rho5.BottomRightVariation.L N)) := by
  obtain ⟨M, N, ε, η, values, hmaxM, hMne, h00M, hposM, hcp0M, hcp4M, hcp3M, hcp2M, hpM, hkM,
    hrM, hvaluesM, -, hratioM, -, -, -, -, hε, hη, hNM, hmaxN, h00N, hpN, hkN, hrN, hsN, htN,
    htraceN, hratioN, -, -, hvaluesN, -, hcmpN⟩ :=
    Rho5.TailSignNormalization.exists_canonical_tail_witness_nonneg h4
  have h00Mne : M 0 0 ≠ 0 := by rw [h00M]; norm_num
  have hpMne : S4 M 0 0 ≠ 0 := ne_of_gt (by simpa [p] using hpM)
  have hkMne : S3 M 0 0 ≠ 0 := ne_of_gt (by simpa [k] using hkM)
  have hcp0N : Rho5.Pivot.IsCompletePivot N 0 0 := by
    rw [hNM]
    exact (Rho5.TailSignNormalization.isCompletePivot_signedEntries5 M hε hη).mpr hcp0M
  have hcp4N : Rho5.Pivot.IsCompletePivot (S4 N) 0 0 := by
    rw [hNM]
    exact (Rho5.TailSignNormalization.isCompletePivot_S4_signedEntries M hε hη h00Mne).mpr hcp4M
  have hcp3N : Rho5.Pivot.IsCompletePivot (S3 N) 0 0 := by
    rw [hNM]
    exact (Rho5.TailSignNormalization.isCompletePivot_S3_signedEntries M hε hη h00Mne hpMne).mpr hcp3M
  have hcp2N : Rho5.Pivot.IsCompletePivot (T2 N) 0 0 := by
    rw [hNM]
    exact (Rho5.TailSignNormalization.isCompletePivot_T2_signedEntries M hε hη h00Mne hpMne
      hkMne).mpr hcp2M
  have hpNpos : 0 < p N := by rw [hpN]; exact hpM
  have hkNpos : 0 < k N := by rw [hkN]; exact hkM
  have hrNpos : 0 < r N := by rw [hrN]; exact hrM
  obtain ⟨hmaxS, h00S, hcp0S, hcp4S, hcp3S, hcp2S, hpS, hkS, hrS, hsS, htS, htraceS, hrhoS,
    hpeakS, hbranchS, hbdS, hcmpS⟩ :=
    shift_L_qualifications h4 hmaxN h00N hcp0N hcp4N hcp3N hcp2N hpNpos hkNpos hrNpos hsN htN
      hvaluesN hratioN hcmpN
  exact ⟨M, N, ε, η, values, hmaxM, hMne, h00M, hposM, hcp0M, hcp4M, hcp3M, hcp2M, hpM, hkM,
    hrM, hvaluesM, hratioM, hε, hη, hNM, hmaxN, h00N, hsN, htN, htraceN, hratioN, hmaxS, h00S,
    hcp0S, hcp4S, hcp3S, hcp2S, hpS, hkS, hrS, hsS, htS, htraceS, hrhoS, hpeakS, hbranchS, hbdS,
    hcmpS⟩

end Rho5.TailBoundaryReduction
