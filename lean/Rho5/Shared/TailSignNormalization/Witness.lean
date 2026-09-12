/-
D53 — 接 D48 实际最大者：非负尾符号的真实全局最大见证
=========================================================

消费 D48 已验收的条件式见证 `exists_canonical_tail_witness`（前提 `4 < rho5Trace`），
再对它应用本卡的整矩阵末位符号规范化，得到同一真实见证的**非负尾符号**版本：

* `M` 与 `values` 保持 D48 的全部资格（四层 CP、`p/k/r > 0`、五值列表、峰值分支、D46 包络、
  原全局比较）；
* 存在 `ε, η ∈ {1,-1}` 与真实整矩阵 `N = signedEntries M (sigma5 ε) (sigma5 η)`，满足
  `0 ≤ s N`、`0 ≤ t N`、`p N = p M`、`k N = k M`、`r N = r M`、`|δ N| = |δ M|`；
* `values` 同时是 `N` 的真实迹，且增长比不变：`growthRatio N values = rho5Trace`，
  原全局比较对 `N` 同样成立，末两步峰值二分对 `N` 也成立。

**保留的前提**：`4 < rho5Trace` 仍是假设（本卡不证明它）；**不**声称满秩、`d = -r`、
全域可平衡或 `rho5 = alpha`。
-/
import Rho5.Shared.TailSignNormalization.Normalize
import Rho5.Shared.CanonicalTail.Witness

namespace Rho5.TailSignNormalization

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D53 主定理（条件式）**：若 `4 < rho5Trace`，则存在真实 `M`、`N`、`ε, η`、`values`，
使 D48 的规范最大见证全部成立，且其末位符号规范化后的整矩阵 `N` 有 `s N ≥ 0`、`t N ≥ 0`、
增长比与全局比较不变。 -/
theorem exists_canonical_tail_witness_nonneg (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N : Matrix5) (ε η : ℝ) (values : List ℝ),
      matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 = 1 ∧
        Rho5.LeadingSigns.LeadingTracePos M values ∧
          Rho5.Pivot.IsCompletePivot M 0 0 ∧ Rho5.Pivot.IsCompletePivot (S4 M) 0 0 ∧
            Rho5.Pivot.IsCompletePivot (S3 M) 0 0 ∧ Rho5.Pivot.IsCompletePivot (T2 M) 0 0 ∧
              0 < p M ∧ 0 < k M ∧ 0 < r M ∧
                values = [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ∧
                  values.length = 5 ∧
                    Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
                      Rho5.GrowthModel.growthRatio M values = Rho5.GrowthModel.tracePeak values ∧
                        (Rho5.GrowthModel.growthRatio M values = r M ∨
                          Rho5.GrowthModel.growthRatio M values =
                            |Rho5.CanonicalTail.delta M|) ∧
                          (4 < r M ∨ 4 < |Rho5.CanonicalTail.delta M|) ∧
                            Rho5.GrowthModel.growthRatio M values ≤ r M + |s M * t M| / r M ∧
                              (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
                                N = Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η) ∧
                                  matrixEntryMax N = 1 ∧ N 0 0 = 1 ∧
                                    p N = p M ∧ k N = k M ∧ r N = r M ∧
                                      0 ≤ s N ∧ 0 ≤ t N ∧
                                        Rho5.CompletePivotPath.LegalTrace N values ∧
                                          Rho5.GrowthModel.growthRatio N values =
                                            Rho5.GrowthSupremum.rho5Trace ∧
                                            Rho5.CanonicalTail.delta N =
                                              ε * η * Rho5.CanonicalTail.delta M ∧
                                              |Rho5.CanonicalTail.delta N| =
                                                |Rho5.CanonicalTail.delta M| ∧
                                                values =
                                                  [1, p N, k N, r N,
                                                    |Rho5.CanonicalTail.delta N|] ∧
                                                  (Rho5.GrowthModel.growthRatio N values = r N ∨
                                                    Rho5.GrowthModel.growthRatio N values =
                                                      |Rho5.CanonicalTail.delta N|) ∧
                                                    ∀ (N' : Matrix5), N' ≠ 0 → ∀ ws : List ℝ,
                                                      Rho5.CompletePivotPath.LegalTrace N' ws →
                                                        Rho5.GrowthModel.growthRatio N' ws ≤
                                                          Rho5.GrowthModel.growthRatio N values := by
  obtain ⟨M, values, hM, hMne, h00, hpos, hcp0, hcp4, hcp3, hcp2, hp, hk, hr, hvalues, hlen,
    hratio, hpeak, hbranch, hbranch4, henv, hcmp⟩ :=
    Rho5.CanonicalTail.exists_canonical_tail_witness h4
  have htraceM : Rho5.CompletePivotPath.LegalTrace M values :=
    Rho5.LeadingTrace.legalTrace_of_leading
      (Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos hpos)
  obtain ⟨ε, η, N, hε, hη, hN, hmaxN, hN00, hpN, hkN, hrN, hsN, htN, hdN, hdeltaN, habsN,
    htraceN, hgrowthN⟩ := exists_nonneg_tail_signs hM h00 hp hk hr htraceM
  refine ⟨M, N, ε, η, values, hM, hMne, h00, hpos, hcp0, hcp4, hcp3, hcp2, hp, hk, hr,
    hvalues, hlen, hratio, hpeak, hbranch, hbranch4, henv, hε, hη, hN, hmaxN, hN00, hpN, hkN,
    hrN, hsN, htN, htraceN, ?_, hdeltaN, habsN, ?_, ?_, ?_⟩
  · rw [hgrowthN]; exact hratio
  · rw [hpN, hkN, hrN, habsN]; exact hvalues
  · rcases hbranch with h | h
    · left; rw [hgrowthN, hrN]; exact h
    · right; rw [hgrowthN, habsN]; exact h
  · intro N' hN' ws hws
    rw [hgrowthN]
    exact hcmp N' hN' ws hws

end Rho5.TailSignNormalization
