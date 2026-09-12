/-
D38 — 峰值连续与紧初始域的峰值集合紧（卡目标 B）
===================================================

**B1.** `v ↦ tracePeak (List.ofFn v)` 连续——`tracePeak` 是有限 `max` 折叠，
按 `List.ofFn_succ`/`tracePeak_cons` 逐阶展开为 `max (v 0) (…)`，由 `Continuous.max` 归纳。

**B2.** 紧初始矩阵集 `C` 的补零峰值集合紧：`isCompact_paddedGraph`（卡目标 A）的像，
沿连续映射 `(A, v) ↦ tracePeak (List.ofFn v)` 取像（`IsCompact.image`）。

**B3.** 用 D35 的精确桥把补零峰值集合换回**原 `LegalTrace`** 的峰值集合：两个方向分别是
`padded_of_legalTrace` + `tracePeak_padList`（补零）与 `exists_legalTrace_of_padded`
（去补零），配合 `exists_ofFn_eq_of_length` 把长度恰为 `n` 的补零列表写成 `List.ofFn`。
因此**原路径**峰值集合也紧——这正是达到性链需要的紧性。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceAttainment.FiberCompact

namespace Rho5.TraceAttainment

open Rho5

/-- **卡目标 B（峰值连续）**：`tracePeak (List.ofFn v)` 关于定长向量 `v` 连续。 -/
theorem continuous_tracePeak_ofFn : ∀ n : ℕ,
    Continuous (fun v : Fin n → ℝ => Rho5.GrowthModel.tracePeak (List.ofFn v))
  | 0 => by
      have h : (fun v : Fin 0 → ℝ => Rho5.GrowthModel.tracePeak (List.ofFn v))
          = fun _ => (0 : ℝ) := by
        funext v
        have hnil : List.ofFn v = ([] : List ℝ) :=
          List.eq_nil_of_length_eq_zero (by simp)
        rw [hnil, Rho5.GrowthModel.tracePeak_nil]
      rw [h]
      exact continuous_const
  | n + 1 => by
      have h : (fun v : Fin (n + 1) → ℝ => Rho5.GrowthModel.tracePeak (List.ofFn v))
          = fun v => max (v 0)
              (Rho5.GrowthModel.tracePeak (List.ofFn fun i => v i.succ)) := by
        funext v
        rw [List.ofFn_succ, Rho5.GrowthModel.tracePeak_cons]
      rw [h]
      exact (continuous_apply 0).max
        ((continuous_tracePeak_ofFn n).comp (continuous_pi fun i => continuous_apply i.succ))

/-- 补零峰值集合就是补零图的像（用于把紧性从图搬到峰值集合）。 -/
theorem paddedPeakSet_eq_image {n : ℕ} (C : Set (Matrix (Fin n) (Fin n) ℝ)) :
    {p : ℝ | ∃ A ∈ C, ∃ v : Fin n → ℝ,
        Rho5.PaddedTrace.PaddedLegalTrace A (List.ofFn v) ∧
          p = Rho5.GrowthModel.tracePeak (List.ofFn v)}
      = (fun x : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
          Rho5.GrowthModel.tracePeak (List.ofFn x.2)) '' paddedGraph n C := by
  ext p
  constructor
  · rintro ⟨A, hA, v, hv, rfl⟩
    exact ⟨(A, v), ⟨hA, hv⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩

/-- **卡目标 B（补零峰值集合紧）**：紧集 `C` 上的补零轨迹峰值集合紧。 -/
theorem isCompact_paddedPeakSet {n : ℕ} {C : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hC : IsCompact C) :
    IsCompact {p : ℝ | ∃ A ∈ C, ∃ v : Fin n → ℝ,
      Rho5.PaddedTrace.PaddedLegalTrace A (List.ofFn v) ∧
        p = Rho5.GrowthModel.tracePeak (List.ofFn v)} := by
  rw [paddedPeakSet_eq_image C]
  exact (isCompact_paddedGraph (n := n) hC).image
    ((continuous_tracePeak_ofFn n).comp continuous_snd)

/-- **卡目标 B（与原 `LegalTrace` 的峰值集合相等）**：D35 桥的两个方向。 -/
theorem legalPeakSet_eq_paddedPeakSet {n : ℕ} (C : Set (Matrix (Fin n) (Fin n) ℝ)) :
    {p : ℝ | ∃ A ∈ C, ∃ values : List ℝ,
        Rho5.CompletePivotPath.LegalTrace A values ∧ p = Rho5.GrowthModel.tracePeak values}
      = {p : ℝ | ∃ A ∈ C, ∃ v : Fin n → ℝ,
        Rho5.PaddedTrace.PaddedLegalTrace A (List.ofFn v) ∧
          p = Rho5.GrowthModel.tracePeak (List.ofFn v)} := by
  ext p
  constructor
  · rintro ⟨A, hA, values, hvalues, rfl⟩
    have hlen : (Rho5.PaddedTrace.padList n values).length = n :=
      Rho5.PaddedTrace.padList_length (Rho5.CompletePivotPath.length_le hvalues)
    obtain ⟨v, hv⟩ := exists_ofFn_eq_of_length hlen
    refine ⟨A, hA, v, ?_, ?_⟩
    · rw [hv]
      exact Rho5.PaddedTrace.padded_of_legalTrace hvalues
    · rw [hv, Rho5.PaddedTrace.tracePeak_padList]
  · rintro ⟨A, hA, v, hv, rfl⟩
    obtain ⟨values, hvalues, hpad⟩ := Rho5.PaddedTrace.exists_legalTrace_of_padded hv
    refine ⟨A, hA, values, hvalues, ?_⟩
    rw [hpad, Rho5.PaddedTrace.tracePeak_padList]

/-- **卡目标 B（原路径峰值集合紧）**：紧初始矩阵集的**真实合法轨迹**峰值集合紧。 -/
theorem isCompact_legalPeakSet {n : ℕ} {C : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hC : IsCompact C) :
    IsCompact {p : ℝ | ∃ A ∈ C, ∃ values : List ℝ,
      Rho5.CompletePivotPath.LegalTrace A values ∧ p = Rho5.GrowthModel.tracePeak values} := by
  rw [legalPeakSet_eq_paddedPeakSet C]
  exact isCompact_paddedPeakSet hC

end Rho5.TraceAttainment
