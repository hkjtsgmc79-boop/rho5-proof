/-
D57 阶段 B — 在可行区间左端 `L` 处保持全局最大性，并保留四选一饱和边界
===========================================================================

**门**：D55 `outputs/heartbeat_0449_delivery_20260912/D55` 的 `BOTTOM_RIGHT_READY` 已验收
（5 源码 / 5 模块 / 41 实际公理；olean 与源哈希均与 READY 记录逐字节一致，见
`results/INPUT_BINDING.json`）。本模块只**读** D55 的已验接口，不复制、不修改其位移/可行性证明。

组装链：

1. 从 D53 的 `exists_canonical_tail_witness_nonneg`（前提 `4 < rho5Trace`）取**符号化规范最大矩阵**
   `N`（`s N ≥ 0`、`t N ≥ 0`、`p/k/r > 0`、四层 CP、`LegalTrace N values`、
   `values = [1, p N, k N, r N, |δ N|]`、`growthRatio N values = rho5Trace`、原全局比较）；
   预符号矩阵 `M` 的四层 CP 经 D53 的**已付运输**（`isCompletePivot_signedEntries*`）转到 `N` 上；
2. 用 D55 的可行区间：`Feasible N h ↔ L N ≤ h ∧ h ≤ U N`，`L N ≤ 0 ≤ U N`，`Feasible N (L N)`，
   以及 `boundary_at_L` 的四选一析取；
3. 阶段 A 的单调性（`tracePeak_five_tail_antitone`，取 `d := T2 N 1 1`、`r := r N`、`s := s N`、
   `t := t N`、`h1 := L N ≤ 0 =: h2`）给出
   `tracePeak (traceValues N 0) ≤ tracePeak (traceValues N (L N))`；
   而 `traceValues N 0 = values`、`tracePeak values = growthRatio N values = rho5Trace`，
   故新矩阵 `N' = shift N (L N)` 的迹峰值 `≥ rho5Trace`，再由 D43 的全局上界取等；
4. 四边界：D55 的 `boundary_at_L` 经 `shift_self`/`S4_shift_33`/`S3_shift_22`/`T2_shift_11` 与
   `p_shift`/`k_shift`/`r_shift` 逐项搬到新矩阵上，**四个分支都保留**。

**不声称**：满秩、`d = -r`、全域可平衡、`4 < rho5Trace`（仍是假设）、`rho5 = alpha`；
也**不**把四分支收敛成"仅平衡尾"。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TailBoundaryReduction.Scalar
import Rho5.Shared.TailBoundaryReduction.ListPeak
import Rho5.Shared.CanonicalMaximizer
import Rho5.Shared.CanonicalTail
import Rho5.Shared.HighGrowthTail
import Rho5.Shared.TailSignNormalization
import Rho5.Shared.BottomRightVariation

namespace Rho5.TailBoundaryReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **阶段 B（条件形式）**：设真实 `N` 满足九个前提与 D53 的尾部数据（`s N, t N ≥ 0`、
`values = [1,p N,k N,r N,|δ N|]`、`growthRatio N values = rho5Trace`、`N` 的原全局比较），
则整矩阵左端位移 `N' = shift N (L N)` 仍然

* 归一化（`matrixEntryMax N' = 1`、`N' 0 0 = 1`）且四层 `(0,0)` 完整主元资格与 `p/k/r > 0` 保持；
* 带真实 `LegalTrace N' (traceValues N (L N))`，且 `s N', t N' ≥ 0` 保持；
* 增长比等于 `rho5Trace`（因此仍是全局最大者，原全局比较照搬到 `N'`）；
* 峰值仍落在第四或第五项（`= r N'` 或 `= |δ N'|`）；
* 四选一饱和边界：`N' 4 4 = -1 ∨ S4 N' 3 3 = -p N' ∨ S3 N' 2 2 = -k N' ∨ T2 N' 1 1 = -r N'`。 -/
theorem shift_L_qualifications {N : Matrix5} {values : List ℝ}
    (h4 : 4 < Rho5.GrowthSupremum.rho5Trace)
    (hmax : matrixEntryMax N = 1) (h00 : N 0 0 = 1)
    (hcp0 : Rho5.Pivot.IsCompletePivot N 0 0) (hcp4 : Rho5.Pivot.IsCompletePivot (S4 N) 0 0)
    (hcp3 : Rho5.Pivot.IsCompletePivot (S3 N) 0 0) (hcp2 : Rho5.Pivot.IsCompletePivot (T2 N) 0 0)
    (hp : 0 < p N) (hk : 0 < k N) (hr : 0 < r N) (hsN : 0 ≤ s N) (htN : 0 ≤ t N)
    (hvalues : values = [1, p N, k N, r N, |Rho5.CanonicalTail.delta N|])
    (hratio : Rho5.GrowthModel.growthRatio N values = Rho5.GrowthSupremum.rho5Trace)
    (hcmp : ∀ M' : Matrix5, M' ≠ 0 → ∀ ws : List ℝ,
      Rho5.CompletePivotPath.LegalTrace M' ws →
        Rho5.GrowthModel.growthRatio M' ws ≤ Rho5.GrowthModel.growthRatio N values) :
    matrixEntryMax (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) = 1 ∧
      Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N) 0 0 = 1 ∧
        Rho5.Pivot.IsCompletePivot (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) 0 0 ∧
          Rho5.Pivot.IsCompletePivot (S4 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))) 0 0 ∧
            Rho5.Pivot.IsCompletePivot (S3 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))) 0 0 ∧
              Rho5.Pivot.IsCompletePivot (T2 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))) 0 0 ∧
                0 < p (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∧
                  0 < k (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∧
                    0 < r (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∧
                      0 ≤ s (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∧
                        0 ≤ t (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∧
                          Rho5.CompletePivotPath.LegalTrace
                            (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                            (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) ∧
                            Rho5.GrowthModel.growthRatio
                              (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                              (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) =
                                Rho5.GrowthSupremum.rho5Trace ∧
                              Rho5.GrowthModel.growthRatio
                                (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                                (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) =
                                  Rho5.GrowthModel.tracePeak
                                    (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) ∧
                                (Rho5.GrowthModel.growthRatio
                                    (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                                    (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) =
                                      r (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∨
                                  Rho5.GrowthModel.growthRatio
                                    (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                                    (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N)) =
                                      |Rho5.CanonicalTail.delta
                                        (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))|) ∧
                                  (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N) 4 4 = -1 ∨
                                    S4 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) 3 3 =
                                      -p (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∨
                                    S3 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) 2 2 =
                                      -k (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) ∨
                                    T2 (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N)) 1 1 =
                                      -r (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))) ∧
                                    (∀ M' : Matrix5, M' ≠ 0 → ∀ ws : List ℝ,
                                      Rho5.CompletePivotPath.LegalTrace M' ws →
                                        Rho5.GrowthModel.growthRatio M' ws ≤
                                          Rho5.GrowthModel.growthRatio
                                            (Rho5.BottomRightVariation.shift N (Rho5.BottomRightVariation.L N))
                                            (Rho5.BottomRightVariation.traceValues N (Rho5.BottomRightVariation.L N))) := by
  set δ := Rho5.CanonicalTail.delta N with hδ
  set Lv := Rho5.BottomRightVariation.L N with hL
  set N' := Rho5.BottomRightVariation.shift N Lv with hN'
  -- D55: feasibility of L and of 0, and L ≤ 0
  have hLfeas : Rho5.BottomRightVariation.Feasible N Lv :=
    Rho5.BottomRightVariation.feasible_L N hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr
  have hLU := Rho5.BottomRightVariation.L_le_zero_le_U N hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr
  have hL0 : Lv ≤ 0 := hLU.1
  have h0U : 0 ≤ Rho5.BottomRightVariation.U N := hLU.2
  have h0feas : Rho5.BottomRightVariation.Feasible N 0 :=
    (Rho5.BottomRightVariation.feasible_iff_interval N 0).mpr ⟨hL0, h0U⟩
  -- the fourth (tail) constraint at 0 and at L, on the corner coordinate T2 N 1 1
  have hc0 : |T2 N 1 1 + 0| ≤ r N := by
    rw [add_zero]
    exact (hcp2 1 1).trans (le_of_eq (abs_of_pos hr))
  have hcL : |T2 N 1 1 + Lv| ≤ r N := hLfeas.2.2.2
  -- traceValues written with the corner coordinate (D55's d) so stage A applies
  have hform : ∀ h : ℝ, Rho5.BottomRightVariation.traceValues N h =
      [1, p N, k N, r N, |T2 N 1 1 + h - t N * s N / r N|] := by
    intro h
    have hin : (T2 N 1 1 - t N * s N / r N) + h = T2 N 1 1 + h - t N * s N / r N := by ring
    simp only [Rho5.BottomRightVariation.traceValues, Rho5.CanonicalTail.delta, hin]
  -- stage A monotonicity: peak at 0 ≤ peak at L
  have hmono : Rho5.GrowthModel.tracePeak (Rho5.BottomRightVariation.traceValues N 0) ≤
      Rho5.GrowthModel.tracePeak (Rho5.BottomRightVariation.traceValues N Lv) := by
    rw [hform 0, hform Lv]
    exact Rho5.TailBoundaryReduction.tracePeak_five_tail_antitone hr hsN htN hcL hc0 hL0
  -- traceValues N 0 is exactly the D53 value list
  have hv0 : Rho5.BottomRightVariation.traceValues N 0 = values := by
    have hid : T2 N 1 1 + 0 - t N * s N / r N = δ := by rw [hδ, Rho5.CanonicalTail.delta]; ring
    rw [hvalues, hform 0, hid]
  have hpeak0 : Rho5.GrowthModel.tracePeak (Rho5.BottomRightVariation.traceValues N 0) =
      Rho5.GrowthSupremum.rho5Trace := by
    rw [hv0, ← Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hmax, hratio]
  -- D55: the shifted matrix carries the actual trace and its growth ratio is the trace peak
  have htrace' : Rho5.CompletePivotPath.LegalTrace N'
      (Rho5.BottomRightVariation.traceValues N Lv) :=
    Rho5.BottomRightVariation.legalTrace_shift N Lv hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr hLfeas
  have hgrowth' : Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) =
      Rho5.GrowthModel.tracePeak (Rho5.BottomRightVariation.traceValues N Lv) :=
    Rho5.BottomRightVariation.growthRatio_shift N Lv hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr hLfeas
  have hmax' : matrixEntryMax N' = 1 :=
    Rho5.BottomRightVariation.matrixEntryMax_shift N Lv hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr hLfeas
  have hN'ne : N' ≠ 0 := by
    intro h0
    have hz : matrixEntryMax (0 : Matrix5) = 0 :=
      (Rho5.MatrixNormalization.matrixEntryMax_eq_zero_iff 0).mpr rfl
    rw [h0, hz] at hmax'
    exact one_ne_zero hmax'.symm
  -- growth ratio is exactly rho5Trace
  have hge : Rho5.GrowthSupremum.rho5Trace ≤
      Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) := by
    rw [hgrowth', ← hpeak0]
    exact hmono
  have hle : Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) ≤
      Rho5.GrowthSupremum.rho5Trace :=
    Rho5.CanonicalMaximizer.growthRatio_le_rho5Trace hN'ne htrace'
  have hrho : Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) =
      Rho5.GrowthSupremum.rho5Trace := le_antisymm hle hge
  -- peak alternative for the shifted trace (D45 branch, both values read off the concrete list)
  have hpeakBranch : Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) = r N' ∨
      Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) =
        |Rho5.CanonicalTail.delta N'| := by
    have hgt : 4 < Rho5.GrowthModel.growthRatio N' (Rho5.BottomRightVariation.traceValues N Lv) := by
      rw [hrho]; exact h4
    have hd3 : (Rho5.BottomRightVariation.traceValues N Lv).getD 3 0 = r N := by
      rw [hform Lv]; simp
    have hd4 : (Rho5.BottomRightVariation.traceValues N Lv).getD 4 0 =
        |Rho5.CanonicalTail.delta N + Lv| := by
      rw [hform Lv]
      have hid : T2 N 1 1 + Lv - t N * s N / r N = Rho5.CanonicalTail.delta N + Lv := by
        rw [Rho5.CanonicalTail.delta]; ring
      rw [hid]; simp
    have hrN' : r N' = r N := Rho5.BottomRightVariation.r_shift N Lv
    have hδN' : Rho5.CanonicalTail.delta N' = Rho5.CanonicalTail.delta N + Lv :=
      Rho5.BottomRightVariation.delta_shift N Lv
    rcases Rho5.HighGrowthTail.peak_is_getD_three_or_four N' hN'ne htrace' hgt with
      ⟨-, hget3, -⟩ | ⟨-, hget4, -⟩
    · left
      rw [hgrowth', ← hget3, hd3, ← hrN']
    · right
      rw [hgrowth', ← hget4, hd4, ← hδN']
  -- the four-way boundary, transported to the shifted matrix
  have hbd : Rho5.BottomRightVariation.shift N Lv 4 4 = -1 ∨
      S4 (Rho5.BottomRightVariation.shift N Lv) 3 3 = -p (Rho5.BottomRightVariation.shift N Lv) ∨
      S3 (Rho5.BottomRightVariation.shift N Lv) 2 2 = -k (Rho5.BottomRightVariation.shift N Lv) ∨
      T2 (Rho5.BottomRightVariation.shift N Lv) 1 1 = -r (Rho5.BottomRightVariation.shift N Lv) := by
    have hb := Rho5.BottomRightVariation.boundary_at_L N hmax h00 hcp0 hcp4 hcp3 hcp2 hp hk hr
    have h44 : Rho5.BottomRightVariation.shift N Lv 4 4 = N 4 4 + Lv :=
      Rho5.BottomRightVariation.shift_self N Lv
    have hS4 : S4 (Rho5.BottomRightVariation.shift N Lv) 3 3 = S4 N 3 3 + Lv :=
      Rho5.BottomRightVariation.S4_shift_33 N Lv
    have hS3 : S3 (Rho5.BottomRightVariation.shift N Lv) 2 2 = S3 N 2 2 + Lv :=
      Rho5.BottomRightVariation.S3_shift_22 N Lv
    have hT2 : T2 (Rho5.BottomRightVariation.shift N Lv) 1 1 = Rho5.BottomRightVariation.d N + Lv := by
      rw [Rho5.BottomRightVariation.T2_shift_11, Rho5.BottomRightVariation.d]
    have hp' : p (Rho5.BottomRightVariation.shift N Lv) = p N :=
      Rho5.BottomRightVariation.p_shift N Lv
    have hk' : k (Rho5.BottomRightVariation.shift N Lv) = k N :=
      Rho5.BottomRightVariation.k_shift N Lv
    have hr' : r (Rho5.BottomRightVariation.shift N Lv) = r N :=
      Rho5.BottomRightVariation.r_shift N Lv
    rcases hb with h | h | h | h
    · exact Or.inl (by rw [h44]; exact h)
    · exact Or.inr (Or.inl (by rw [hS4, hp']; exact h))
    · exact Or.inr (Or.inr (Or.inl (by rw [hS3, hk']; exact h)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hT2, hr']; exact h)))
  refine ⟨hmax', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htrace', hrho, hgrowth', hpeakBranch, hbd, ?_⟩
  · rw [hN', Rho5.BottomRightVariation.shift_of_ne_left N Lv (by decide : (0 : Fin 5) ≠ 4), h00]
  · exact (Rho5.BottomRightVariation.isCompletePivot_shift_iff N Lv hmax h00 hcp0).mpr hLfeas.1
  · exact (Rho5.BottomRightVariation.isCompletePivot_S4_shift_iff N Lv hcp4 hp).mpr hLfeas.2.1
  · exact (Rho5.BottomRightVariation.isCompletePivot_S3_shift_iff N Lv hcp3 hk).mpr hLfeas.2.2.1
  · exact (Rho5.BottomRightVariation.isCompletePivot_T2_shift_iff N Lv hcp2 hr).mpr hLfeas.2.2.2
  · rw [Rho5.BottomRightVariation.p_shift N Lv]; exact hp
  · rw [Rho5.BottomRightVariation.k_shift N Lv]; exact hk
  · rw [Rho5.BottomRightVariation.r_shift N Lv]; exact hr
  · rw [Rho5.BottomRightVariation.s_shift N Lv]; exact hsN
  · rw [Rho5.BottomRightVariation.t_shift N Lv]; exact htN
  · intro M' hM' ws hws
    rw [hrho]
    exact le_trans (hcmp M' hM' ws hws) (le_of_eq hratio)

end Rho5.TailBoundaryReduction
