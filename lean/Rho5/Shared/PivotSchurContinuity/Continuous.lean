/-
D32 — 含零点的 Schur 连续性
=============================

**卡目标 3.** 对任意 `n`、`p q : Fin (n+1)`：

  `ContinuousOn (fun A => pivotSchur A p q) (CPDomain p q)`。

**A = 0 处明确处理.** `CPDomain p q` 上唯一可能使主元为零的点是 `A = 0`
（目标 1），而 `pivotSchur 0 p q = 0`。零点的连续性用**目标 2 的条目估计**做挤压：

  `|pivotSchur A p q i j| ≤ 2 * |A p q|` 且 `A ↦ A p q` 在零点连续（在集合内也趋于 `0`），
  于是每个坐标趋于 `0`，由 `tendsto_pi_nhds` 得到矩阵值映射趋于 `0 = pivotSchur 0 p q`。

**非零主元处用连续除法.** 主元非零时，D10 的 `pivotSchur_apply` 给出一个处处相等的显式
公式（分母 `A p q` 在 `A` 处非零），公式是连续函数经 `sub`/`mul`/`div` 的组合
（`ContinuousAt.div`），故 `ContinuousAt`，进而是集合内的 `ContinuousWithinAt`。

**既不假设后继主元非零，也不假设“除法处处连续”**：除法只在“分母在该点非零”的
`ContinuousAt.div` 形式下使用；在零点走的是上面的估计路线，而不是把 `1 / A p q`
当作处处连续。坐标拓扑用的是 D26 已声明的实矩阵乘积拓扑实例。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.PivotSchurContinuity.Bound
import Mathlib.Topology.MetricSpace.Bounded

namespace Rho5.PivotSchurContinuity

open Rho5 Filter
open scoped Topology

/-- D10 `pivotSchur_apply` 右侧的**显式公式映射**（作为矩阵值函数）。
它处处等于 `pivotSchur · p q`，但它的除法项在 `A p q = 0` 处没有数学意义——
这正是必须分情形的原因。 -/
noncomputable def schurFormula {n : ℕ} (p q : Fin (n + 1))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    A (Rho5.PivotReindex.remainingIndex p i) (Rho5.PivotReindex.remainingIndex q j)
      - A (Rho5.PivotReindex.remainingIndex p i) q
        * A p (Rho5.PivotReindex.remainingIndex q j) / A p q

/-- `pivotSchur` 与显式公式**处处相等**（D10 的 `pivotSchur_apply`，无任何前提）。 -/
theorem pivotSchur_eq_schurFormula {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p q : Fin (n + 1)) : Rho5.PivotReindex.pivotSchur A p q = schurFormula p q A := by
  funext i j
  exact Rho5.PivotReindex.pivotSchur_apply A p q i j

/-- 非零主元处公式连续：每个坐标是 `sub`/`mul`/`div` 的组合，除法的分母 `A p q` 在该点非零。 -/
theorem continuousAt_schurFormula_of_pivot_ne_zero {n : ℕ} {p q : Fin (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hpq : A p q ≠ 0) :
    ContinuousAt (schurFormula p q) A := by
  -- `Matrix` is a semireducible def, so the Pi lemmas need the coordinate form explicitly
  change ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    fun i j : Fin n => schurFormula p q B i j) A
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  -- the point is implicit in `Continuous.continuousAt`; the ascriptions pin it down
  have h1 : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      B (Rho5.PivotReindex.remainingIndex p i) (Rho5.PivotReindex.remainingIndex q j)) A :=
    (continuous_matrix_entry _ _).continuousAt
  have h2 : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      B (Rho5.PivotReindex.remainingIndex p i) q) A :=
    (continuous_matrix_entry _ _).continuousAt
  have h3 : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      B p (Rho5.PivotReindex.remainingIndex q j)) A :=
    (continuous_matrix_entry _ _).continuousAt
  have h4 : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => B p q) A :=
    (continuous_matrix_entry _ _).continuousAt
  exact h1.sub ((h2.mul h3).div h4 hpq)

/-- 非零主元处 `pivotSchur · p q` 连续（由公式处处相等搬运）。 -/
theorem continuousAt_pivotSchur_of_pivot_ne_zero {n : ℕ} {p q : Fin (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hpq : A p q ≠ 0) :
    ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      Rho5.PivotReindex.pivotSchur B p q) A := by
  have hfun : (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      Rho5.PivotReindex.pivotSchur B p q) = schurFormula p q := by
    funext B
    exact pivotSchur_eq_schurFormula B p q
  rw [hfun]
  exact continuousAt_schurFormula_of_pivot_ne_zero hpq

/-- **零点处的连续性**：在 `𝓝[CPDomain p q] 0` 下 `pivotSchur · p q` 趋于
`pivotSchur 0 p q = 0`。

证明：每个坐标由目标 2 的估计 `|pivotSchur A p q i j| ≤ 2 * |A p q|` 夹住，
而 `A ↦ |A p q|` 在集合内趋于 `0`；逐坐标得到 Pi 收敛。 -/
theorem tendsto_pivotSchur_zero {n : ℕ} (p q : Fin (n + 1)) :
    Tendsto (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      Rho5.PivotReindex.pivotSchur A p q) (𝓝[CPDomain p q] 0) (𝓝 0) := by
  -- coordinate form of the matrix-valued limit (again: `Matrix` does not unfold for `rw`)
  change Tendsto (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      fun i j : Fin n => Rho5.PivotReindex.pivotSchur A p q i j)
    (𝓝[CPDomain p q] 0) (𝓝 (fun _ _ : Fin n => (0 : ℝ)))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpqt : Tendsto (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => |A p q|)
      (𝓝[CPDomain p q] 0) (𝓝 0) := by
    have h : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => B p q)
        (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
      (continuous_matrix_entry _ _).continuousAt
    have h2 : ContinuousWithinAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => |B p q|)
        (CPDomain p q) 0 := h.continuousWithinAt.abs
    -- spell the Tendsto out (ContinuousWithinAt *is* a Tendsto), then simplify |0| = 0
    have h3 : Tendsto (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => |B p q|)
        (𝓝[CPDomain p q] 0) (𝓝 (|(0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q|)) := h2
    simpa using h3
  have hev : ∀ᶠ A in 𝓝[CPDomain p q] 0, |A p q| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hpqt) (ε / 2) (half_pos hε)
    simpa [Real.dist_eq, sub_zero] using h
  filter_upwards [hev, self_mem_nhdsWithin] with A hlt hA
  calc dist (Rho5.PivotReindex.pivotSchur A p q i j) 0
      = |Rho5.PivotReindex.pivotSchur A p q i j| := by rw [Real.dist_eq, sub_zero]
    _ ≤ 2 * |A p q| := pivotSchur_entry_abs_le_two_mul_pivot hA i j
    _ < ε := by linarith

/-- **卡目标 3（主定理）**：`A ↦ pivotSchur A p q` 在 `CPDomain p q` 上连续。

分情形：`A p q = 0` 时 `A = 0`，用 `tendsto_pivotSchur_zero`（零点估计）；
否则用非零主元处的连续除法。 -/
theorem continuousOn_pivotSchur {n : ℕ} (p q : Fin (n + 1)) :
    ContinuousOn (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      Rho5.PivotReindex.pivotSchur A p q) (CPDomain p q) := by
  intro A hA
  by_cases hpq : A p q = 0
  · have hA0 : A = 0 := eq_zero_of_mem_CPDomain_of_pivot_eq_zero hA hpq
    subst hA0
    have hz : Rho5.PivotReindex.pivotSchur (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) p q = 0 :=
      pivotSchur_zero p q
    show Tendsto (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      Rho5.PivotReindex.pivotSchur B p q) (𝓝[CPDomain p q] 0)
      (𝓝 (Rho5.PivotReindex.pivotSchur 0 p q))
    rw [hz]
    exact tendsto_pivotSchur_zero p q
  · exact (continuousAt_pivotSchur_of_pivot_ne_zero hpq).continuousWithinAt

end Rho5.PivotSchurContinuity
