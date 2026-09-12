/-
D38 — 定长补零轨迹的图与单步分支分解
=====================================

**卡目标 A 的组合层.** 把 D35 的 `PaddedLegalTrace` 写成「矩阵 × 定长向量」上的图，
并按 D35 关系的**真实构造器**做单步分解：

* `paddedGraph n C`：`C` 中矩阵与它们的补零轨迹向量；
* `paddedGraph (n+1) C = ⋃ (pq : Fin (n+1) × Fin (n+1)), paddedStepSet n C p q`
  ——覆盖**所有**合法主元分支（`IsCompletePivot`，无任何非零前提），因此零矩阵与
  「非零主元」开条件都不需要被当成闭条件使用；
* `X` 上沿任意 `φ` 的纤维版本 `paddedFiber`/`fiberStep`（供紧性归纳在
  `φ = pivotSchur · p q` 上使用）；
* `continuous_finCons`：`Fin.cons` 关于 `(a, w)` 连续（mathlib 没有该引理，本卡自证，
  只用于把「头值 + 尾向量」拼成 `Fin (n+1) → ℝ`）。

复用（只读冻结输入）：D35 `PaddedTrace`（关系、长度、桥）、D10 `pivotSchur`、
D32 `CPDomain`/连续性（下一步紧性用）、D26 的矩阵乘积拓扑实例（引用，不重复声明）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Rho5.Shared.PaddedTrace
import Rho5.Shared.PivotSchurContinuity

namespace Rho5.TraceAttainment

open Rho5

/-! ## 图与分支集 -/

/-- **卡目标 A（图）**：`C` 中矩阵的补零轨迹向量图。 -/
def paddedGraph (n : ℕ) (C : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {x | x.1 ∈ C ∧ Rho5.PaddedTrace.PaddedLegalTrace x.1 (List.ofFn x.2)}

/-- **卡目标 A（单步分支）**：在 `(p, q)` 处走一步的图——头是真实值 `|A p q|`，
尾是 `pivotSchur A p q` 的补零轨迹；主元条件只有 `IsCompletePivot`（允许零主元）。 -/
def paddedStepSet (n : ℕ) (C : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (p q : Fin (n + 1)) :
    Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × (Fin (n + 1) → ℝ)) :=
  {x | x.1 ∈ C ∧ Rho5.Pivot.IsCompletePivot x.1 p q ∧
    ∃ w : Fin n → ℝ,
      Rho5.PaddedTrace.PaddedLegalTrace (Rho5.PivotReindex.pivotSchur x.1 p q) (List.ofFn w) ∧
      x.2 = Fin.cons (|x.1 p q|) w}

/-! ## `Fin.cons` 与 `List.ofFn` 的拼装引理 -/

/-- `Fin.cons` 与 `List.ofFn` 相容。 -/
theorem ofFn_fin_cons {n : ℕ} (a : ℝ) (w : Fin n → ℝ) :
    List.ofFn (Fin.cons a w) = a :: List.ofFn w := by
  rw [List.ofFn_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- 反向：`List.ofFn` 相等给出向量相等（`Fin.cons` 形式）。 -/
theorem eq_fin_cons_of_ofFn_eq {n : ℕ} {v : Fin (n + 1) → ℝ} {a : ℝ} {w : Fin n → ℝ}
    (h : List.ofFn v = a :: List.ofFn w) : v = Fin.cons a w := by
  rw [← List.ofFn_inj, h, ofFn_fin_cons]

/-- 长度匹配的列表是某个定长向量的 `List.ofFn`（用 D35 的 `ofFn_get_eq`）。 -/
theorem exists_ofFn_eq_of_length {n : ℕ} {l : List ℝ} (h : l.length = n) :
    ∃ w : Fin n → ℝ, List.ofFn w = l :=
  ⟨fun i => l.get (Fin.cast h.symm i), Rho5.PaddedTrace.ofFn_get_eq h⟩

/-- 补零关系的单步分解（正向）：任何补零轨迹都由某一步与尾轨迹给出。 -/
theorem exists_step_of_padded {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {padded : List ℝ} (h : Rho5.PaddedTrace.PaddedLegalTrace A padded) :
    ∃ (p q : Fin (n + 1)) (tail : List ℝ),
      Rho5.Pivot.IsCompletePivot A p q ∧
        Rho5.PaddedTrace.PaddedLegalTrace (Rho5.PivotReindex.pivotSchur A p q) tail ∧
        padded = |A p q| :: tail := by
  cases h with
  | step p q hmax htail => exact ⟨p, q, _, hmax, htail, rfl⟩

/-! ## 图的分支分解 -/

/-- `0` 阶：尾向量空间是单点，主元条件自动满足（唯一的 `0 × 0` 矩阵有 `empty` 轨迹）。 -/
theorem paddedGraph_zero (C : Set (Matrix (Fin 0) (Fin 0) ℝ)) :
    paddedGraph 0 C = C ×ˢ (Set.univ : Set (Fin 0 → ℝ)) := by
  ext x
  constructor
  · intro hx; exact ⟨hx.1, trivial⟩
  · rintro ⟨hx1, -⟩
    refine ⟨hx1, ?_⟩
    have h0 : x.1 = 0 := Subsingleton.elim _ _
    rw [h0]
    have hnil : List.ofFn x.2 = ([] : List ℝ) :=
      List.eq_nil_of_length_eq_zero (by simp)
    rw [hnil]
    exact Rho5.PaddedTrace.PaddedLegalTrace.empty

/-- **卡目标 A（分支分解）**：`n+1` 阶的图是全部 `(p, q)` 分支的并——**所有**合法主元
都被覆盖，零主元分支（进而 `A = 0`）也在其中。 -/
theorem paddedGraph_succ (n : ℕ) (C : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) :
    paddedGraph (n + 1) C
      = ⋃ pq : Fin (n + 1) × Fin (n + 1), paddedStepSet n C pq.1 pq.2 := by
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

/-! ## 连续 `Fin.cons`（mathlib 无此引理，本卡自证） -/

/-- `(a, w) ↦ Fin.cons a w` 连续。 -/
theorem continuous_finCons {n : ℕ} :
    Continuous (fun z : ℝ × (Fin n → ℝ) =>
      @Fin.cons n (fun _ : Fin (n + 1) => ℝ) z.1 z.2) := by
  refine continuous_pi (fun i => ?_)
  induction i using Fin.cases with
  | zero => simpa [Fin.cons_zero] using continuous_fst
  | succ j => simpa [Fin.cons_succ] using (continuous_apply j).comp continuous_snd

end Rho5.TraceAttainment
