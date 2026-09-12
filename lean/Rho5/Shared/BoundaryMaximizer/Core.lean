/-
D68 阶段 A — 排序四边界最大者的**转置不变核心事实包**
=========================================================

D57 的阶段 B 已交付**实际**四边界最大者 `S = shift N (L N)`：它达到 `rho5Trace`、
带真实 `LegalTrace`、四层完整主元、`p/k/r > 0`、`0 ≤ s, t`，并落在四选一饱和边界上。
D63 交付**整矩阵转置**的排序选择与对角不变性。

本文件只做两件事：

* 把 D57/D63 已付的"五阶固定事实"打包成两个具名结构：
  `BoundaryMaximizerCore`（转置不变部分）与 `SortedBoundaryMaximizerFacts`
  （再追加 `0 ≤ s ≤ t`，由 `Sorted.lean` 的实际存在性定理填充）；
* 证明核心包在**整矩阵转置**下保持 —— 四个边界面都是对角条目（`(4,4)`、`S4 (3,3)`、
  `S3 (2,2)`、`T2 (1,1)`），而 `p/k/r`、真实迹值表、`LegalTrace`、增长比与原全局比较
  都转置不变，故"四选一"的四个面在换序后**一个不少**（不把四分支收敛为某一支）。

**不声称**：`4 < rho5Trace`（仅在阶段 A 主定理里作显式前提）、满秩、`d = -r`、
全域可平衡、`rho5 = alpha`、新的覆盖性或唯一性。
-/
import Rho5.Shared.TailTransposeOrder
import Rho5.Shared.BottomRightVariation

namespace Rho5.BoundaryMaximizer

open scoped Matrix
open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **五阶固定事实的转置不变核心**（D68 阶段 A 的具名事实包）：`P` 是归一化的实际非零整
矩阵（`P 0 0 = 1` 且最大条目为 `1`），带四层完整主元资格、`p/k/r > 0`、真实迹值表
`[1, p P, k P, r P, |δ P|]`、真实 `LegalTrace`、增长比恰为 `rho5Trace`、
**四选一饱和边界全保留**，并且仍是**原全矩阵/全迹比较**下的最大者。 -/
structure BoundaryMaximizerCore (P : Matrix5) (values : List ℝ) : Prop where
  /-- 实际非零（由归一化条目直接给出）。 -/
  ne_zero : P ≠ 0
  /-- 归一化：最大条目为 `1`。 -/
  entryMax : matrixEntryMax P = 1
  /-- 归一化：`P 0 0 = 1`。 -/
  zero_zero : P 0 0 = 1
  /-- 第一层完整主元资格。 -/
  cp0 : Rho5.Pivot.IsCompletePivot P 0 0
  /-- 第二层（`S4`）完整主元资格。 -/
  cp4 : Rho5.Pivot.IsCompletePivot (S4 P) 0 0
  /-- 第三层（`S3`）完整主元资格。 -/
  cp3 : Rho5.Pivot.IsCompletePivot (S3 P) 0 0
  /-- 尾块（`T2`）完整主元资格。 -/
  cp2 : Rho5.Pivot.IsCompletePivot (T2 P) 0 0
  /-- 第二主元读数严格为正。 -/
  p_pos : 0 < p P
  /-- 第三主元读数严格为正。 -/
  k_pos : 0 < k P
  /-- 尾主元读数严格为正。 -/
  r_pos : 0 < r P
  /-- **真实迹值表**：迹值就是实际四阶读数与尾读数。 -/
  trace_eq : values = [1, p P, k P, r P, |Rho5.CanonicalTail.delta P|]
  /-- **真实 `LegalTrace`**（D13/D37 的完整主元路径，非人工列表）。 -/
  legal : Rho5.CompletePivotPath.LegalTrace P values
  /-- **仍是全局最大者**：增长比恰为 `rho5Trace`。 -/
  growth_eq_rho : Rho5.GrowthModel.growthRatio P values = Rho5.GrowthSupremum.rho5Trace
  /-- **四选一饱和边界全保留**（四个面，不合并、不排序）。 -/
  boundary : P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨ T2 P 1 1 = -r P
  /-- **原全矩阵/全迹比较**：对任意非零 `M'` 与任意合法迹值表 `ws`。 -/
  global_max : ∀ (M' : Matrix5), M' ≠ 0 → ∀ ws : List ℝ,
    Rho5.CompletePivotPath.LegalTrace M' ws →
      Rho5.GrowthModel.growthRatio M' ws ≤ Rho5.GrowthModel.growthRatio P values

/-- **排序后的实际四边界最大者**：核心事实包 + `0 ≤ s P ≤ t P`
（排序由 D63 的整矩阵转置选择给出，见 `Sorted.lean` 的实际存在性定理）。 -/
structure SortedBoundaryMaximizerFacts (P : Matrix5) (values : List ℝ) : Prop
    extends BoundaryMaximizerCore P values where
  /-- 排序左端非负。 -/
  s_nonneg : 0 ≤ s P
  /-- 排序：`s ≤ t`。 -/
  s_le_t : s P ≤ t P

/-- **D55 `traceValues` 的变动后形态**：`traceValues N h` 恰是**位移后矩阵自身**的四阶读数
与尾读数表 `[1, p (shift N h), k (shift N h), r (shift N h), |δ (shift N h)|]`。
（`p/k/r` 与 `δ` 在 `shift` 下分别不变与平移 `delta_shift`。） -/
theorem traceValues_shift_eq (N : Matrix5) (h : ℝ) :
    Rho5.BottomRightVariation.traceValues N h =
      [1, p (Rho5.BottomRightVariation.shift N h), k (Rho5.BottomRightVariation.shift N h),
        r (Rho5.BottomRightVariation.shift N h),
        |Rho5.CanonicalTail.delta (Rho5.BottomRightVariation.shift N h)|] := by
  rw [Rho5.BottomRightVariation.traceValues_eq, ← Rho5.BottomRightVariation.p_shift N h,
    ← Rho5.BottomRightVariation.k_shift N h, ← Rho5.BottomRightVariation.r_shift N h,
    ← Rho5.BottomRightVariation.delta_shift N h]

/-- **核心事实包在整矩阵转置下保持**：四个边界面都是对角条目，`p/k/r`、真实迹值表、
`LegalTrace`、增长比与原全局比较全部转置不变，故四个饱和面一个不少。 -/
theorem BoundaryMaximizerCore.transpose {P : Matrix5} {values : List ℝ}
    (h : BoundaryMaximizerCore P values) : BoundaryMaximizerCore Pᵀ values :=
  { ne_zero := fun h0 => h.ne_zero (by
      have h1 : (Pᵀ)ᵀ = (0 : Matrix5)ᵀ := congrArg Matrix.transpose h0
      simpa using h1),
    entryMax := by
      rw [Rho5.TraceTranspose.matrixEntryMax_transpose P]
      exact h.entryMax,
    zero_zero := by
      rw [Rho5.TraceTranspose.transpose_zero_zero P]
      exact h.zero_zero,
    cp0 := (Rho5.TailTransposeOrder.isCompletePivot_transpose P).1.mpr h.cp0,
    cp4 := (Rho5.TailTransposeOrder.isCompletePivot_transpose P).2.1.mpr h.cp4,
    cp3 := (Rho5.TailTransposeOrder.isCompletePivot_transpose P).2.2.1.mpr h.cp3,
    cp2 := (Rho5.TailTransposeOrder.isCompletePivot_transpose P).2.2.2.mpr h.cp2,
    p_pos := by
      rw [Rho5.TailTransposeOrder.p_transpose P]
      exact h.p_pos,
    k_pos := by
      rw [Rho5.TailTransposeOrder.k_transpose P]
      exact h.k_pos,
    r_pos := by
      rw [Rho5.TailTransposeOrder.r_transpose P]
      exact h.r_pos,
    trace_eq := by
      rw [Rho5.TailTransposeOrder.p_transpose P, Rho5.TailTransposeOrder.k_transpose P,
        Rho5.TailTransposeOrder.r_transpose P, Rho5.TailTransposeOrder.delta_transpose P]
      exact h.trace_eq,
    legal := Rho5.TraceTranspose.legalTrace_transpose_iff.mpr h.legal,
    growth_eq_rho := by
      rw [Rho5.TraceTranspose.growthRatio_transpose P values]
      exact h.growth_eq_rho,
    boundary := by
      obtain ⟨h44, hS4, hS3, -, hp, hk, hr⟩ := Rho5.TailTransposeOrder.diag_transpose P
      rw [h44, hS4, hS3, hp, hk, hr, Rho5.TailTransposeOrder.d_transpose P]
      exact h.boundary,
    global_max := fun M' hM' ws hws => by
      rw [Rho5.TraceTranspose.growthRatio_transpose P values]
      exact h.global_max M' hM' ws hws }

end Rho5.BoundaryMaximizer
