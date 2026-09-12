/-
D38 — 定长补零轨迹图的紧性（卡目标 A 的核心）
===============================================

**定理（纤维形式）**：对任意拓扑空间 `X`、紧集 `C ⊆ X` 与**在 `C` 上连续**的
`φ : X → Matrix (Fin n) (Fin n) ℝ`，集合

  `{(x, w) : X × (Fin n → ℝ) | x ∈ C ∧ PaddedLegalTrace (φ x) (List.ofFn w)}`

紧。

**归纳结构**（对 `n`，覆盖全部合法主元分支，包括零矩阵）：

* `n = 0`：尾向量空间是单点、`0 × 0` 矩阵只有 `empty` 轨迹，故集合就是 `C × univ`，
  是紧集 `C` 在连续单射 `x ↦ (x, ·)` 下的像；
* `n + 1`：按 D35 的真实构造器把图拆成有限并
  `⋃ (p q), paddedStepSet`。对每一支：
  1. `C' := {x ∈ C | IsCompletePivot (φ x) p q}` 紧——`CPDomain p q` 闭（D32），
     用 `ContinuousOn.preimage_isClosed_of_isClosed` 与 `IsCompact.isClosed`；
  2. `φ' x := pivotSchur (φ x) p q` 在 `C'` 上连续——`φ` 在 `C` 上连续 + D32 的
     `continuousOn_pivotSchur`，经 `ContinuousOn.comp` 与 `MapsTo`（`C'` 的定义就是映射条件）；
  3. 归纳假设给出尾图紧，再用**连续**的拼接映射
     `Λ (x, w) = (x, Fin.cons (|φ x p q|) w)`（`continuous_finCons` + 条目连续性）取像。

**关键点（回应卡片警告）**：主元非零是**开**条件，本证明从不把它当闭条件；分支约束只用到
`IsCompletePivot`（闭）与**已证的** Schur 连续性，零主元分支（此时 `A = 0`）作为有限并的一项
被同一套论证覆盖；不假设全路径图紧、也不挑选单一路径。

**桥实例**：`T2Space (Matrix m n ℝ)` 显式取坐标空间的 Pi 实例（`Matrix` 是半可约 `def`，
实例搜索不展开它）。这是与 D26 拓扑实例**不同**的 typeclass，不是重复声明同一个实例。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.TraceAttainment.Graph

namespace Rho5.TraceAttainment

open Rho5

/-- 桥实例：实矩阵空间的 T2 性（取坐标空间 `m → n → ℝ` 的 Pi 实例）。
D26 只声明了乘积拓扑实例；`Matrix` 半可约，`T2Space` 也需要显式桥接。 -/
instance instT2SpaceMatrix {m n : Type*} : T2Space (Matrix m n ℝ) :=
  inferInstanceAs (T2Space (m → n → ℝ))

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- 沿 `φ` 的纤维图。 -/
def paddedFiber (n : ℕ) (C : Set X) (φ : X → Matrix (Fin n) (Fin n) ℝ) :
    Set (X × (Fin n → ℝ)) :=
  {x | x.1 ∈ C ∧ Rho5.PaddedTrace.PaddedLegalTrace (φ x.1) (List.ofFn x.2)}

/-- 沿 `φ` 的单步分支（全部合法主元，含零主元）。 -/
def fiberStep (n : ℕ) (C : Set X) (φ : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) : Set (X × (Fin (n + 1) → ℝ)) :=
  {x | x.1 ∈ C ∧ Rho5.Pivot.IsCompletePivot (φ x.1) p q ∧
    ∃ w : Fin n → ℝ,
      Rho5.PaddedTrace.PaddedLegalTrace (Rho5.PivotReindex.pivotSchur (φ x.1) p q) (List.ofFn w) ∧
      x.2 = Fin.cons (|φ x.1 p q|) w}

/-! ## 分解与像表示 -/

omit [TopologicalSpace X] [T2Space X] in
theorem paddedFiber_zero (C : Set X) (φ : X → Matrix (Fin 0) (Fin 0) ℝ) :
    paddedFiber 0 C φ = C ×ˢ (Set.univ : Set (Fin 0 → ℝ)) := by
  ext x
  constructor
  · intro hx; exact ⟨hx.1, trivial⟩
  · rintro ⟨hx1, -⟩
    refine ⟨hx1, ?_⟩
    have h0 : φ x.1 = 0 := Subsingleton.elim _ _
    rw [h0]
    have hnil : List.ofFn x.2 = ([] : List ℝ) := List.eq_nil_of_length_eq_zero (by simp)
    rw [hnil]
    exact Rho5.PaddedTrace.PaddedLegalTrace.empty

omit [TopologicalSpace X] [T2Space X] in
theorem paddedFiber_succ (n : ℕ) (C : Set X)
    (φ : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    paddedFiber (n + 1) C φ
      = ⋃ pq : Fin (n + 1) × Fin (n + 1), fiberStep n C φ pq.1 pq.2 := by
  ext x
  constructor
  · rintro ⟨hxC, htrace⟩
    obtain ⟨p, q, tail, hmax, htail, hEq⟩ := exists_step_of_padded htrace
    obtain ⟨w, hw⟩ := exists_ofFn_eq_of_length (Rho5.PaddedTrace.padded_length htail)
    refine Set.mem_iUnion.mpr ⟨(p, q), hxC, hmax, w, ?_, ?_⟩
    · rwa [hw]
    · apply eq_fin_cons_of_ofFn_eq
      rw [hEq, hw]
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨pq, hxC, hmax, w, hw, hv⟩
    refine ⟨hxC, ?_⟩
    rw [hv, ofFn_fin_cons]
    exact Rho5.PaddedTrace.PaddedLegalTrace.step pq.1 pq.2 hmax hw

omit [TopologicalSpace X] [T2Space X] in
theorem fiberStep_eq_image (n : ℕ) (C : Set X)
    (φ : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    fiberStep n C φ p q
      = (fun y : X × (Fin n → ℝ) => (y.1, Fin.cons (|φ y.1 p q|) y.2)) ''
        paddedFiber n {x | x ∈ C ∧ Rho5.Pivot.IsCompletePivot (φ x) p q}
          (fun x => Rho5.PivotReindex.pivotSchur (φ x) p q) := by
  ext x
  constructor
  · rintro ⟨hxC, hmax, w, hw, hv⟩
    refine ⟨(x.1, w), ⟨⟨hxC, hmax⟩, ?_⟩, ?_⟩
    · show Rho5.PaddedTrace.PaddedLegalTrace
        (Rho5.PivotReindex.pivotSchur (φ x.1) p q) (List.ofFn w)
      exact hw
    · exact Prod.ext rfl hv.symm
  · rintro ⟨y, ⟨hyC, hytrace⟩, rfl⟩
    exact ⟨hyC.1, hyC.2, y.2, hytrace, rfl⟩

/-! ## 单步分支紧 -/

/-- **卡目标 A（纤维形式）**：紧集上、沿 `C` 上连续的 `φ` 的补零轨迹图紧。

对 `n` 归纳；`n+1` 时按分支并展开，每一支用 `C' := {x ∈ C | IsCompletePivot (φ x) p q}`
（紧，因 `CPDomain` 闭且 `φ` 在 `C` 上连续）与归纳假设，再取连续拼接映射的像。 -/
theorem isCompact_paddedFiber : ∀ (n : ℕ) (C : Set X) (φ : X → Matrix (Fin n) (Fin n) ℝ),
    IsCompact C → ContinuousOn φ C → IsCompact (paddedFiber n C φ)
  | 0, C, φ, hC, _ => by
      rw [paddedFiber_zero]
      have himg : C ×ˢ (Set.univ : Set (Fin 0 → ℝ))
          = (fun x : X => (x, fun _ : Fin 0 => (0 : ℝ))) '' C := by
        ext y
        constructor
        · rintro ⟨hy1, -⟩
          exact ⟨y.1, hy1, Prod.ext rfl (Subsingleton.elim _ _)⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨hx, trivial⟩
      rw [himg]
      exact hC.image (continuous_id.prodMk continuous_const)
  | n + 1, C, φ, hC, hφ => by
      rw [paddedFiber_succ]
      refine isCompact_iUnion (fun pq => ?_)
      -- 单步分支的紧性（就地证明，归纳假设即本定理的递归调用）
      have hC'closed : IsClosed (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2) :=
        ContinuousOn.preimage_isClosed_of_isClosed hφ hC.isClosed
          (Rho5.PivotSchurContinuity.isClosed_CPDomain pq.1 pq.2)
      have hC' : IsCompact (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2) :=
        hC.of_isClosed_subset hC'closed Set.inter_subset_left
      have hφ' : ContinuousOn
          (fun x : X => Rho5.PivotReindex.pivotSchur (φ x) pq.1 pq.2)
          (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2) :=
        (Rho5.PivotSchurContinuity.continuousOn_pivotSchur pq.1 pq.2).comp
          (hφ.mono Set.inter_subset_left) (fun _ hx => hx.2)
      have hIH : IsCompact (paddedFiber n (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2)
          (fun x => Rho5.PivotReindex.pivotSchur (φ x) pq.1 pq.2)) :=
        isCompact_paddedFiber n _ _ hC' hφ'
      have hentry : ContinuousOn (fun y : X × (Fin n → ℝ) => |φ y.1 pq.1 pq.2|)
          (paddedFiber n (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2)
            (fun x => Rho5.PivotReindex.pivotSchur (φ x) pq.1 pq.2)) :=
        ((continuous_abs.comp ((continuous_apply pq.2).comp (continuous_apply pq.1))).comp_continuousOn
          (hφ.comp continuousOn_fst (fun y hy => hy.1.1)))
      have hpair : ContinuousOn (fun y : X × (Fin n → ℝ) => (|φ y.1 pq.1 pq.2|, y.2))
          (paddedFiber n (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2)
            (fun x => Rho5.PivotReindex.pivotSchur (φ x) pq.1 pq.2)) :=
        hentry.prodMk continuousOn_snd
      have hΛ : ContinuousOn
          (fun y : X × (Fin n → ℝ) =>
            (y.1, @Fin.cons n (fun _ : Fin (n + 1) => ℝ) (|φ y.1 pq.1 pq.2|) y.2))
          (paddedFiber n (C ∩ φ ⁻¹' Rho5.PivotSchurContinuity.CPDomain pq.1 pq.2)
            (fun x => Rho5.PivotReindex.pivotSchur (φ x) pq.1 pq.2)) :=
        continuousOn_fst.prodMk (continuous_finCons.comp_continuousOn hpair)
      rw [fiberStep_eq_image]
      exact hIH.image_of_continuousOn hΛ

/-- **卡目标 A（原形式）**：任何紧矩阵集的定长补零轨迹图紧。 -/
theorem isCompact_paddedGraph {n : ℕ} {C : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hC : IsCompact C) : IsCompact (paddedGraph n C) :=
  isCompact_paddedFiber n C id hC continuous_id.continuousOn

end Rho5.TraceAttainment
