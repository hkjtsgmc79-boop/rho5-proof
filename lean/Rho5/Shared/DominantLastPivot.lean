/-
D59 — 实际支配末主元：严格符号与行列式
=======================================

1. **标量尾事实**：`r > 0`、`s, t ≥ 0`、`|d| ≤ r`、`δ = d - t*s/r` 时

   * `δ ≤ r`；
   * 若 `max r |δ| > r`，则 `δ < 0`、`max r |δ| = -δ`，且 `s > 0`、`t > 0`
     （严格非对角正性由 `t*s/r > r + d ≥ 0` 推出，不是假设）。

   平移到实际 `T2 M` 时**保留完整主元资格**（`Rho5.Pivot.IsCompletePivot (T2 M) 0 0`）。

2. **精确二分**：对 D53 修正后的非负规范见证（`s N, t N ≥ 0`，来自 D48 的条件式规范最大者，
   仍以 `4 < rho5Trace` 为显式前提）记 `g = growthRatio N values = rho5Trace`，则

   `g = r N` **或**（`r N < g` 且 `δ N = -g` 且 `s N > 0` 且 `t N > 0`）；

   第四主元支路原样保留，增长定义不被改写，整矩阵符号规范化（`N = signedEntries M …`）
   与真实 `LegalTrace`、全局比较一并保留。

3. **严格分支的行列式**（消费 D56）：`δ N = -g`、`g > 0` 时

   `det N = -(p N * k N * r N * g) < 0` 且 `det N ≠ 0`；非零性由严格分支证明，
   **不**从 `values.length` 或仅 `p/k/r > 0` 推出。条件推论：`4 < g` 与 `r ≤ 4`
   一起给出该严格分支（`r ≤ 4` 始终是显式假设，本卡不建立四阶尖锐上界）。

4. **全局最大者二分**：`4 < rho5Trace` 下，实际规范全局最大者的两种可能：
   第四主元 `= rho5Trace` 且 `> 4`，或末主元严格分支（`s, t > 0`、负非零行列式与精确公式）。

**不声明**：平衡尾、alpha 尖锐性、`4 < rho` 本身，也不在没有证明的情况下消去第一个分支。
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Rho5.Shared.TailDeterminant
import Rho5.Shared.TailSignNormalization

namespace Rho5.DominantLastPivot

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. 标量尾事实 -/

/-- **目标 1（上界）**：`0 < r`、`0 ≤ s`、`0 ≤ t`、`|d| ≤ r` 时 `δ = d - t*s/r ≤ r`
（`t*s/r ≥ 0` 且 `d ≤ |d| ≤ r`）。 -/
theorem delta_le_r {r s t d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hd : |d| ≤ r) :
    d - t * s / r ≤ r := by
  have h1 : 0 ≤ t * s / r := div_nonneg (mul_nonneg ht hs) (le_of_lt hr)
  have h2 : d ≤ |d| := le_abs_self d
  linarith

/-- **目标 1（严格负）**：`max r |δ| > r` 时 `δ < 0` 且 `max r |δ| = -δ`。 -/
theorem delta_neg_of_max_gt {r s t d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d| ≤ r) (hmax : r < max r |d - t * s / r|) :
    d - t * s / r < 0 ∧ max r |d - t * s / r| = -(d - t * s / r) := by
  have hle := delta_le_r hr hs ht hd
  have hcase : max r |d - t * s / r| = |d - t * s / r| := by
    rcases le_total r |d - t * s / r| with h | h
    · exact max_eq_right h
    · exact absurd (max_eq_left h) (ne_of_gt hmax)
  have habs : r < |d - t * s / r| := by rw [← hcase]; exact hmax
  have hneg : d - t * s / r < 0 := by
    by_contra hcon
    have h0 : 0 ≤ d - t * s / r := le_of_not_gt hcon
    rw [abs_of_nonneg h0] at habs
    linarith
  refine ⟨hneg, ?_⟩
  rw [hcase, abs_of_neg hneg]

/-- **目标 1（严格非对角正性）**：同一前提下 `s > 0` 且 `t > 0`。
关键中间量是 `t*s/r > r + d ≥ 0`：`δ < 0` 与 `max r |δ| = -δ` 给出 `t*s/r - d > r`，
再由 `d ≥ -r` 得严格正。 -/
theorem s_pos_and_t_pos_of_max_gt {r s t d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d| ≤ r) (hmax : r < max r |d - t * s / r|) : 0 < s ∧ 0 < t := by
  obtain ⟨hneg, hmaxeq⟩ := delta_neg_of_max_gt hr hs ht hd hmax
  have habs : r < -(d - t * s / r) := by linarith [hmax, hmaxeq]
  have hdge : -r ≤ d := (abs_le.mp hd).1
  have hts : 0 < t * s / r := by linarith
  have hts' : 0 < t * s := by
    have := mul_pos hts hr
    rwa [div_mul_cancel₀ _ (ne_of_gt hr)] at this
  rcases mul_pos_iff.mp hts' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h2, h1⟩
  · exact absurd h1 (not_lt_of_ge ht)

/-- **目标 1（合并版）**：`δ < 0`、`max r |δ| = -δ`、`s > 0`、`t > 0` 四条一次给出。 -/
theorem strict_tail_of_max_gt {r s t d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d| ≤ r) (hmax : r < max r |d - t * s / r|) :
    d - t * s / r < 0 ∧ max r |d - t * s / r| = -(d - t * s / r) ∧ 0 < s ∧ 0 < t := by
  obtain ⟨hneg, hmaxeq⟩ := delta_neg_of_max_gt hr hs ht hd hmax
  obtain ⟨hsp, htp⟩ := s_pos_and_t_pos_of_max_gt hr hs ht hd hmax
  exact ⟨hneg, hmaxeq, hsp, htp⟩

/-- **目标 2 的抽象二分**：给定 `δ = d - t*s/r`、`0 ≤ s,t`、`|d| ≤ r`、`0 < r`、
峰值二分 `g = r ∨ g = |δ|` 与 `r ≤ g`，则

`g = r` **或**（`r < g ∧ δ = -g ∧ s > 0 ∧ t > 0`）。

第四主元支路（`g = r`）原样保留，不被消去。 -/
theorem alternative_of_branch {r s t d g : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d| ≤ r) (hbranch : g = r ∨ g = |d - t * s / r|) (hgr : r ≤ g) :
    g = r ∨ (r < g ∧ d - t * s / r = -g ∧ 0 < s ∧ 0 < t) := by
  rcases hbranch with h | h
  · exact Or.inl h
  · by_cases hgr' : g = r
    · exact Or.inl hgr'
    · have hlt : r < g := lt_of_le_of_ne hgr (Ne.symm hgr')
      have hmax : r < max r |d - t * s / r| := by
        have habs : r < |d - t * s / r| := by rw [← h]; exact hlt
        rwa [max_eq_right (le_of_lt habs)]
      obtain ⟨hneg, hmaxeq⟩ := delta_neg_of_max_gt hr hs ht hd hmax
      obtain ⟨hsp, htp⟩ := s_pos_and_t_pos_of_max_gt hr hs ht hd hmax
      refine Or.inr ⟨hlt, ?_, hsp, htp⟩
      rw [h, abs_of_neg hneg]
      ring

/-! ## 2. 实际 `T2` 版（保留完整主元资格） -/

/-- **目标 1（实际 `T2` 的条目界）**：`T2 M` 在 `(0,0)` 有真实完整主元且 `0 < r M` 时
`|T2 M 1 1| ≤ r M`（`(1,1)` 处的 CP 实例 + `|T2 M 0 0| = r M`）。 -/
theorem abs_T2_one_one_le_r (M : Matrix5) (hcp : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hr : 0 < r M) : |T2 M 1 1| ≤ r M := by
  have hr_eq : |T2 M 0 0| = r M := by rw [← r]; exact abs_of_pos hr
  have h := hcp 1 1
  rwa [hr_eq] at h

/-- **目标 1（实际 `T2` 版）**：把标量结论平移到真实尾块，完整主元资格作为显式输入保留。 -/
theorem strict_tail_of_max_gt_T2 (M : Matrix5) (hcp : Rho5.Pivot.IsCompletePivot (T2 M) 0 0)
    (hr : 0 < r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M)
    (hmax : r M < max (r M) |Rho5.CanonicalTail.delta M|) :
    Rho5.CanonicalTail.delta M < 0 ∧
      max (r M) |Rho5.CanonicalTail.delta M| = -Rho5.CanonicalTail.delta M ∧
        0 < s M ∧ 0 < t M := by
  have hd : |T2 M 1 1| ≤ r M := abs_T2_one_one_le_r M hcp hr
  have h := strict_tail_of_max_gt hr hs ht hd hmax
  simpa only [Rho5.CanonicalTail.delta] using h

/-! ## 3. 严格分支的行列式（消费 D56） -/

/-- **目标 3（严格分支的行列式）**：`δ M = -g` 且 `g > 0` 时，D56 的
`det M = p M * k M * r M * δ M` 给出

`det M = -(p M * k M * r M * g) < 0` 且 `det M ≠ 0`。

这里的非零性来自严格分支本身（`δ M = -g < 0`），**不**来自 `values.length` 或仅
`p/k/r > 0`。 -/
theorem det_eq_neg_of_delta_eq_neg (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) {g : ℝ} (hg : 0 < g)
    (hdelta : Rho5.CanonicalTail.delta M = -g) :
    M.det = -(p M * k M * r M * g) ∧ M.det < 0 ∧ M.det ≠ 0 := by
  have hdet := Rho5.TailDeterminant.det_eq_prod_delta M h00 (ne_of_gt hp) (ne_of_gt hk)
    (ne_of_gt hr)
  have hval : M.det = -(p M * k M * r M * g) := by
    rw [hdet, hdelta]; ring
  have hpos : 0 < p M * k M * r M * g := mul_pos (mul_pos (mul_pos hp hk) hr) hg
  have hneg : -(p M * k M * r M * g) < 0 := by linarith
  exact ⟨hval, hval ▸ hneg, hval ▸ ne_of_lt hneg⟩

/-- **目标 3（条件推论）**：`4 < g` 与 `r ≤ 4` 一起给出 `r < g`，即严格末主元分支所需的
严格性；`r ≤ 4` 是显式假设，本卡不建立四阶尖锐上界。 -/
theorem r_lt_of_four_lt_of_le_four {r g : ℝ} (hg : 4 < g) (hr : r ≤ 4) : r < g :=
  lt_of_le_of_lt hr hg

/-! ## 4. 实际规范全局最大者的二分 -/

/-- **目标 4（全局最大者二分）**：`4 < rho5Trace` 下存在真实 `M`（条件式规范最大者）、
整矩阵符号规范化 `N = signedEntries M (sigma5 ε) (sigma5 η)`（故 `s N, t N ≥ 0` 是**已付的
整矩阵变换**，不是孤立尾块编辑）、真实值列表 `values` 与 `g = growthRatio N values = rho5Trace`，
使 `N` 归一化（`matrixEntryMax N = 1`、`N ≠ 0`、`N 0 0 = 1`）、携带真实 `LegalTrace`、
保留原全局比较，并且恰有下列二者之一：

* 第四主元支路：`g = r N` 且 `4 < r N`；
* 严格末主元分支：`r N < g`、`δ N = -g`、`s N > 0`、`t N > 0`，且
  `N.det = -(p N * k N * r N * g) < 0`、`N.det ≠ 0`。 -/
theorem exists_global_maximizer_alternative (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N : Matrix5) (ε η : ℝ) (values : List ℝ) (g : ℝ),
      N = Rho5.TraceSigns.signedEntries M (Rho5.TailSignNormalization.sigma5 ε)
        (Rho5.TailSignNormalization.sigma5 η) ∧
        (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
          matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 = 1 ∧
            Rho5.LeadingSigns.LeadingTracePos M values ∧
              Rho5.Pivot.IsCompletePivot M 0 0 ∧
                Rho5.Pivot.IsCompletePivot (S4 M) 0 0 ∧
                  Rho5.Pivot.IsCompletePivot (S3 M) 0 0 ∧
                    Rho5.Pivot.IsCompletePivot (T2 M) 0 0 ∧
                      0 < p M ∧ 0 < k M ∧ 0 < r M ∧
                        values = [1, p M, k M, r M, |Rho5.CanonicalTail.delta M|] ∧
                          Rho5.GrowthModel.growthRatio M values =
                            Rho5.GrowthSupremum.rho5Trace ∧
                            matrixEntryMax N = 1 ∧ N ≠ 0 ∧ N 0 0 = 1 ∧
                              p N = p M ∧ k N = k M ∧ r N = r M ∧
                                0 ≤ s N ∧ 0 ≤ t N ∧
                                  Rho5.CompletePivotPath.LegalTrace N values ∧
                                    values = [1, p N, k N, r N,
                                      |Rho5.CanonicalTail.delta N|] ∧
                                      g = Rho5.GrowthModel.growthRatio N values ∧
                                        g = Rho5.GrowthSupremum.rho5Trace ∧
                                          (∀ (N' : Matrix5), N' ≠ 0 → ∀ ws : List ℝ,
                                            Rho5.CompletePivotPath.LegalTrace N' ws →
                                              Rho5.GrowthModel.growthRatio N' ws ≤ g) ∧
                                            ( (g = r N ∧ 4 < r N) ∨
                                              (r N < g ∧ Rho5.CanonicalTail.delta N = -g ∧
                                                0 < s N ∧ 0 < t N ∧
                                                  N.det = -(p N * k N * r N * g) ∧
                                                    N.det < 0 ∧ N.det ≠ 0) ) := by
  obtain ⟨M, N, ε, η, values, hM, hMne, h00, hpos, hcp0, hcp4, hcp3, hcp2, hp, hk, hr,
    hvalues, _hlen, hratio, hpeak, _hbranch, _hbranch4, _henv, hε, hη, hN, hmaxN, hN00, hpN,
    hkN, hrN, hsN, htN, htraceN, hgrowthN, _hdeltaN, _habsN, hvaluesN, hbranchN, hcmp⟩ :=
    Rho5.TailSignNormalization.exists_canonical_tail_witness_nonneg h4
  have h00ne : M 0 0 ≠ 0 := by rw [h00]; exact one_ne_zero
  have hpne : S4 M 0 0 ≠ 0 := ne_of_gt (by simpa [p] using hp)
  have hkne : S3 M 0 0 ≠ 0 := ne_of_gt (by simpa [k] using hk)
  have hT2N : T2 N 1 1 = ε * η * (T2 M 1 1) := by
    rw [hN]
    exact Rho5.TailSignNormalization.d_signedEntries M hε hη h00ne hpne hkne
  have hTM : |T2 M 1 1| ≤ r M := abs_T2_one_one_le_r M hcp2 hr
  have hεη : |ε * η| = 1 := by
    rcases hε with h | h <;> rcases hη with h' | h' <;> simp [h, h']
  have hdN : |T2 N 1 1| ≤ r N := by
    rw [hT2N, abs_mul, hεη, one_mul, hrN]
    exact hTM
  have hrNpos : 0 < r N := by rw [hrN]; exact hr
  have hpeakN : Rho5.GrowthModel.growthRatio N values = Rho5.GrowthModel.tracePeak values := by
    rw [hgrowthN, ← hratio, hpeak]
  have hrN_le_g : r N ≤ Rho5.GrowthModel.growthRatio N values := by
    rw [hpeakN]
    exact Rho5.GrowthModel.le_tracePeak (by rw [hvaluesN]; simp)
  have halt : Rho5.GrowthModel.growthRatio N values = r N ∨
      (r N < Rho5.GrowthModel.growthRatio N values ∧
        Rho5.CanonicalTail.delta N = -Rho5.GrowthModel.growthRatio N values ∧
          0 < s N ∧ 0 < t N) := by
    have h := alternative_of_branch hrNpos hsN htN hdN hbranchN hrN_le_g
    simpa only [Rho5.CanonicalTail.delta] using h
  have hg4 : 4 < Rho5.GrowthModel.growthRatio N values := by rw [hgrowthN]; exact h4
  have hNne : N ≠ 0 := by
    intro h
    have h0 : N 0 0 = 0 := by rw [h]; rfl
    rw [hN00] at h0
    exact one_ne_zero h0
  refine ⟨M, N, ε, η, values, Rho5.GrowthModel.growthRatio N values, hN, hε, hη, hM, hMne,
    h00, hpos, hcp0, hcp4, hcp3, hcp2, hp, hk, hr, hvalues, hratio, hmaxN, hNne, hN00, hpN, hkN,
    hrN, hsN, htN, htraceN, hvaluesN, rfl, hgrowthN, hcmp, ?_⟩
  rcases halt with h | h
  · left
    exact ⟨h, by rw [← h]; exact hg4⟩
  · right
    obtain ⟨hlt, hdelta, hsp, htp⟩ := h
    have hgpos : 0 < Rho5.GrowthModel.growthRatio N values := by linarith
    have hdet := det_eq_neg_of_delta_eq_neg N hN00 (by rw [hpN]; exact hp)
      (by rw [hkN]; exact hk) hrNpos hgpos hdelta
    exact ⟨hlt, hdelta, hsp, htp, hdet.1, hdet.2.1, hdet.2.2⟩

/-- **目标 2（精确二分，保留规范/迹/全局比较）**：目标 4 的见证在**不丢弃第四主元支路**的
前提下给出卡上要求的二分 `g = r N ∨ (r N < g ∧ δ N = -g ∧ s N > 0 ∧ t N > 0)`。 -/
theorem exists_dominant_last_pivot_alternative (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M N : Matrix5) (ε η : ℝ) (values : List ℝ) (g : ℝ),
      N = Rho5.TraceSigns.signedEntries M (Rho5.TailSignNormalization.sigma5 ε)
        (Rho5.TailSignNormalization.sigma5 η) ∧
        (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
          matrixEntryMax N = 1 ∧ N ≠ 0 ∧ N 0 0 = 1 ∧
            Rho5.LeadingSigns.LeadingTracePos M values ∧
              Rho5.CompletePivotPath.LegalTrace N values ∧
                0 ≤ s N ∧ 0 ≤ t N ∧
                  values = [1, p N, k N, r N, |Rho5.CanonicalTail.delta N|] ∧
                    g = Rho5.GrowthModel.growthRatio N values ∧
                      g = Rho5.GrowthSupremum.rho5Trace ∧
                        (∀ (N' : Matrix5), N' ≠ 0 → ∀ ws : List ℝ,
                          Rho5.CompletePivotPath.LegalTrace N' ws →
                            Rho5.GrowthModel.growthRatio N' ws ≤ g) ∧
                          (g = r N ∨
                            (r N < g ∧ Rho5.CanonicalTail.delta N = -g ∧
                              0 < s N ∧ 0 < t N)) := by
  obtain ⟨M, N, ε, η, values, g, hN, hε, hη, _hM, _hMne, _h00, hpos, _hcp0, _hcp4, _hcp3,
    _hcp2, _hp, _hk, _hr, _hvalues, _hratio, hmaxN, hNne, hN00, _hpN, _hkN, _hrN, hsN, htN,
    htraceN, hvaluesN, hg, hgrho, hcmp, halt⟩ :=
    exists_global_maximizer_alternative h4
  refine ⟨M, N, ε, η, values, g, hN, hε, hη, hmaxN, hNne, hN00, hpos, htraceN, hsN, htN,
    hvaluesN, hg, hgrho, hcmp, ?_⟩
  rcases halt with ⟨h1, _⟩ | h2
  · exact Or.inl h1
  · exact Or.inr ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩

end Rho5.DominantLastPivot
