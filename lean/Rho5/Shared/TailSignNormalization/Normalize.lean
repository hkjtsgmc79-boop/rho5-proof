/-
D53 — 末位符号规范化：δ 变换与「s、t 非负」的真实整矩阵
=========================================================

在 D22 运输（`Transport`）之上：

* `δ N = ε * η * δ M`、`|δ N| = |δ M|`（`δ = d - t*s/r`，`d = T2 · 1 1`）；
* 四层 `(0,0)` 的完整主元资格在符号变换下**保持**；
* `matrixEntryMax`、`M 0 0 = 1`、原 `LegalTrace` 值列表与增长比全部保持（D22）；
* **选择** `ε = if 0 ≤ t M then 1 else -1`、`η = if 0 ≤ s M then 1 else -1`（零取 `+1`），
  得到真实整矩阵 `N = signedEntries M (sigma5 ε) (sigma5 η)`，满足 `0 ≤ s N`、`0 ≤ t N`。

没有任何平衡尾块假设（不假设 `d = -r`），没有满秩假设，也没有新公理。
-/
import Rho5.Shared.TailSignNormalization.Transport
import Rho5.Shared.CanonicalTail

namespace Rho5.TailSignNormalization

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## δ 的符号变换 -/

/-- **δ 变换**：`δ N = ε * η * δ M`（实数除法全定义，无需 `r ≠ 0`）。 -/
theorem delta_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    Rho5.CanonicalTail.delta (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) =
      ε * η * Rho5.CanonicalTail.delta M := by
  rw [Rho5.CanonicalTail.delta, Rho5.CanonicalTail.delta,
    d_signedEntries M hε hη h00 hp hk, t_signedEntries M hε hη h00 hp hk,
    s_signedEntries M hε hη h00 hp hk, r_signedEntries M hε hη h00 hp hk,
    div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **δ 的绝对值不变**：`|δ N| = |δ M|`。 -/
theorem abs_delta_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    |Rho5.CanonicalTail.delta (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η))| =
      |Rho5.CanonicalTail.delta M| := by
  rw [delta_signedEntries M hε hη h00 hp hk]
  have h1 : |ε * η| = 1 := by
    rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> norm_num
  rw [abs_mul, h1, one_mul]

/-! ## 四层完整主元资格的保持 -/

theorem isCompletePivot_signedEntries5 (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) :
    Rho5.Pivot.IsCompletePivot (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) 0 0 ↔
      Rho5.Pivot.IsCompletePivot M 0 0 :=
  Rho5.TraceSigns.isCompletePivot_signedEntries_iff M (isSign_sigma5 hε) (isSign_sigma5 hη) 0 0

theorem isCompletePivot_S4_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) :
    Rho5.Pivot.IsCompletePivot
        (S4 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η))) 0 0 ↔
      Rho5.Pivot.IsCompletePivot (S4 M) 0 0 := by
  rw [S4_signedEntries M hε hη h00]
  exact Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S4 M) (isSign_sigma4 hε)
    (isSign_sigma4 hη) 0 0

theorem isCompletePivot_S3_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) :
    Rho5.Pivot.IsCompletePivot
        (S3 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η))) 0 0 ↔
      Rho5.Pivot.IsCompletePivot (S3 M) 0 0 := by
  rw [S3_signedEntries M hε hη h00 hp]
  exact Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S3 M) (isSign_sigma3 hε)
    (isSign_sigma3 hη) 0 0

theorem isCompletePivot_T2_signedEntries (M : Matrix5) {ε η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hη : η = 1 ∨ η = -1) (h00 : M 0 0 ≠ 0) (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    Rho5.Pivot.IsCompletePivot
        (T2 (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η))) 0 0 ↔
      Rho5.Pivot.IsCompletePivot (T2 M) 0 0 := by
  rw [T2_signedEntries M hε hη h00 hp hk]
  exact Rho5.TraceSigns.isCompletePivot_signedEntries_iff (T2 M) (isSign_sigma2 hε)
    (isSign_sigma2 hη) 0 0

/-! ## 选择末位符号使 `s`、`t` 非负（零取 `+1`） -/

/-- **主定理（整矩阵末位符号规范化）**：给定真实 `M`（`matrixEntryMax M = 1`、`M 0 0 = 1`、
`p M > 0`、`k M > 0`、`r M > 0`）与真实迹 `values`，存在 `ε, η ∈ {1,-1}` 与真实整矩阵
`N = signedEntries M (sigma5 ε) (sigma5 η)`，使 `s N ≥ 0`、`t N ≥ 0`，同时

* `matrixEntryMax N = 1`、`N 0 0 = 1`、`p N = p M`、`k N = k M`、`r N = r M`；
* `T2 N 1 1 = ε * η * (T2 M 1 1)`、`δ N = ε * η * δ M`、`|δ N| = |δ M|`；
* 原 `LegalTrace` 值列表 `values` 与增长比都不变（D22）。

`ε`/`η` 取 `if 0 ≤ t M then 1 else -1` 与 `if 0 ≤ s M then 1 else -1`，零一律取 `+1`。 -/
theorem exists_nonneg_tail_signs {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hp : 0 < p M) (hk : 0 < k M) (_hr : 0 < r M)
    (htrace : Rho5.CompletePivotPath.LegalTrace M values) :
    ∃ (ε η : ℝ) (N : Matrix5),
      (ε = 1 ∨ ε = -1) ∧ (η = 1 ∨ η = -1) ∧
        N = Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η) ∧
          matrixEntryMax N = 1 ∧ N 0 0 = 1 ∧
            p N = p M ∧ k N = k M ∧ r N = r M ∧ 0 ≤ s N ∧ 0 ≤ t N ∧
              T2 N 1 1 = ε * η * (T2 M 1 1) ∧
                Rho5.CanonicalTail.delta N = ε * η * Rho5.CanonicalTail.delta M ∧
                  |Rho5.CanonicalTail.delta N| = |Rho5.CanonicalTail.delta M| ∧
                    Rho5.CompletePivotPath.LegalTrace N values ∧
                      Rho5.GrowthModel.growthRatio N values =
                        Rho5.GrowthModel.growthRatio M values := by
  have h00ne : M 0 0 ≠ 0 := by rw [h00]; norm_num
  have hpne : S4 M 0 0 ≠ 0 := ne_of_gt (by simpa [p] using hp)
  have hkne : S3 M 0 0 ≠ 0 := ne_of_gt (by simpa [k] using hk)
  set ε : ℝ := if 0 ≤ t M then 1 else -1 with hεdef
  set η : ℝ := if 0 ≤ s M then 1 else -1 with hηdef
  have hε : ε = 1 ∨ ε = -1 := by rw [hεdef]; split <;> simp
  have hη : η = 1 ∨ η = -1 := by rw [hηdef]; split <;> simp
  have hsT : Rho5.TraceSigns.IsSign (sigma5 ε) := isSign_sigma5 hε
  have hsS : Rho5.TraceSigns.IsSign (sigma5 η) := isSign_sigma5 hη
  set N : Matrix5 := Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η) with hNdef
  have hmaxN : matrixEntryMax N = 1 := by
    rw [hNdef, ← Rho5.TraceSigns.signedEntries5_eq_signedEntries,
      Rho5.TraceSigns.matrixEntryMax_signedEntries5 M hsT hsS, hM]
  have hN00 : N 0 0 = 1 := by
    rw [hNdef, Rho5.TraceSigns.signedEntries_apply]
    simp [h00]
  have hpN : p N = p M := by rw [hNdef]; exact p_signedEntries M hε hη h00ne
  have hkN : k N = k M := by rw [hNdef]; exact k_signedEntries M hε hη h00ne hpne
  have hrN : r N = r M := by rw [hNdef]; exact r_signedEntries M hε hη h00ne hpne hkne
  have hsN : 0 ≤ s N := by
    rw [hNdef]
    have hs : s (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = η * s M :=
      s_signedEntries M hε hη h00ne hpne hkne
    rw [hs, hηdef]
    split_ifs with h
    · simpa using h
    · have hlt : s M < 0 := lt_of_not_ge h
      nlinarith
  have htN : 0 ≤ t N := by
    rw [hNdef]
    have ht : t (Rho5.TraceSigns.signedEntries M (sigma5 ε) (sigma5 η)) = ε * t M :=
      t_signedEntries M hε hη h00ne hpne hkne
    rw [ht, hεdef]
    split_ifs with h
    · simpa using h
    · have hlt : t M < 0 := lt_of_not_ge h
      nlinarith
  have hdN : T2 N 1 1 = ε * η * (T2 M 1 1) := by
    rw [hNdef]; exact d_signedEntries M hε hη h00ne hpne hkne
  have hdeltaN : Rho5.CanonicalTail.delta N = ε * η * Rho5.CanonicalTail.delta M := by
    rw [hNdef]; exact delta_signedEntries M hε hη h00ne hpne hkne
  have habsN : |Rho5.CanonicalTail.delta N| = |Rho5.CanonicalTail.delta M| := by
    rw [hNdef]; exact abs_delta_signedEntries M hε hη h00ne hpne hkne
  have htraceN : Rho5.CompletePivotPath.LegalTrace N values := by
    rw [hNdef]
    exact (Rho5.TraceSigns.legalTrace_signed_iff' M hsT hsS values).mpr htrace
  have hgrowthN : Rho5.GrowthModel.growthRatio N values =
      Rho5.GrowthModel.growthRatio M values := by
    rw [hNdef, ← Rho5.TraceSigns.signedEntries5_eq_signedEntries,
      Rho5.TraceSigns.growthRatio_signedEntries5 hsT hsS values]
  exact ⟨ε, η, N, hε, hη, hNdef, hmaxN, hN00, hpN, hkN, hrN, hsN, htN, hdN, hdeltaN, habsN,
    htraceN, hgrowthN⟩

end Rho5.TailSignNormalization
