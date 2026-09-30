/-
D135 — Stage B 基础模块：可计算列表检查器 + 到冻结 `Fin` 规则的等价桥
=====================================================================

Stage A 冻结的 `Linear.nonnegCheck` 是**规则**，但定义在 `Finset.univ` 上（`Fin` 索引）。
对具体终端数据做内核求值时，`Finset.sum`/`Matrix.vecCons` 投影的归约并不总是可靠；本模块
不改动、不重审 Stage A 的任何定义，只补一层**纯结构递归的列表实现**和一组**等价桥引理**：

* `dotL` / `colL` / `combL` / `boxMinFrom` / `boxMinL` / `checkL`：列表版检查器，
  只用 `List.zip`/`List.foldr`/`List.getD`/`min`/整数算术，内核可直接求值；
* `sum_fin_getD_mul`、`getD_colL`、`sum_fin_rows_eq_combL`、`sum_fin_boxMinFrom`：
  把 `Fin` 索引的 `Finset` 求和**证明**为等于列表递归（一次证明、对所有数据通用；
  只用 `Fin.sum_univ_succ` 与 `List` 的定义方程，没有新的数学假设）；
* `checkL_eq_true` / `checkL_eq_false`：列表检查器的判定展开。

样本模块的用法：`decide` 得到 `checkL … = true`（内核精确整数算术，无 `native_decide`、
无浮点、无求解器），再用桥把 `nonnegCheck S w = true` 归约到冻结的 `nonnegCheck_sound`。
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases
import Rho5.Shared.CertificateRules.Linear

namespace Rho5.Shared.CertificateRules.ListCheck

set_option linter.unusedSimpArgs false

open scoped BigOperators

/-! ## 列表版检查器（内核可计算） -/

/-- 列表逐点积 `Σ_i w_i * r_i`：`List.zip` + `List.foldr`，纯结构递归。 -/
def dotL (w r : List ℤ) : ℤ :=
  (w.zip r).foldr (fun p acc => p.1 * p.2 + acc) 0

/-- 第 `j` 列的系数向量 `(a_{0,j}, a_{1,j}, …)`。 -/
def colL (rows : List (List ℤ)) (j : Nat) : List ℤ :=
  rows.map (fun r => r.getD j 0)

/-- 组合系数 `C_j = Σ_i w_i a_{i,j}`（列表版）。 -/
def combL (rows : List (List ℤ)) (w : List ℤ) (j : Nat) : ℤ :=
  dotL w (colL rows j)

/-- 从列下标 `k` 起的盒下确界 `Σ_j min (C_{k+j} L_j) (C_{k+j} U_j)`（逐项结构递归）。 -/
def boxMinFrom (rows : List (List ℤ)) (w : List ℤ) : List ℤ → List ℤ → Nat → ℤ
  | [], _, _ => 0
  | _ :: _, [], _ => 0
  | a :: t, b :: u, k =>
      min (combL rows w k * a) (combL rows w k * b) + boxMinFrom rows w t u (k + 1)

/-- 盒下确界 `m = Σ_j min (C_j L_j) (C_j U_j)`（列表版）。 -/
def boxMinL (lo hi : List ℤ) (rows : List (List ℤ)) (w : List ℤ) : ℤ :=
  boxMinFrom rows w lo hi 0

/-- **列表版精确检查器**：`B < m`。可判定、无浮点、无 `native_decide`，内核可求值。 -/
def checkL (lo hi : List ℤ) (rows : List (List ℤ)) (rhs w : List ℤ) : Bool :=
  decide (dotL w rhs < boxMinL lo hi rows w)

/-- `checkL = true` 的展开形式。 -/
theorem checkL_eq_true (lo hi : List ℤ) (rows : List (List ℤ)) (rhs w : List ℤ) :
    checkL lo hi rows rhs w = true ↔ dotL w rhs < boxMinL lo hi rows w := by
  simp [checkL]

/-- `checkL = false` 的展开形式（负控制用：检查失败只是一个假命题，不是执行器错误）。 -/
theorem checkL_eq_false (lo hi : List ℤ) (rows : List (List ℤ)) (rhs w : List ℤ) :
    checkL lo hi rows rhs w = false ↔ ¬ dotL w rhs < boxMinL lo hi rows w := by
  simp [checkL]

/-! ## `getD` 的定义方程（自证 `rfl`，不依赖具体库名） -/

@[simp] theorem cons_getD_zero (a : ℤ) (l : List ℤ) (d : ℤ) :
    (a :: l).getD 0 d = a := rfl

@[simp] theorem cons_getD_succ (a : ℤ) (l : List ℤ) (n : Nat) (d : ℤ) :
    (a :: l).getD (n + 1) d = l.getD n d := rfl

/-! ## 桥引理（符号证明，与具体数据无关） -/

/-- **桥 1（一维求和）**：`Fin` 索引的 `Finset` 求和等于列表折叠。 -/
theorem sum_fin_getD_mul (w r : List ℤ) (h : w.length = r.length) :
    (∑ i : Fin w.length, w.getD i.val 0 * r.getD i.val 0) = dotL w r := by
  induction w generalizing r with
  | nil =>
      cases r with
      | nil => simp [dotL]
      | cons b u => simp at h
  | cons a t ih =>
      cases r with
      | nil => simp at h
      | cons b u =>
          have h' : t.length = u.length := by simpa using h
          rw [List.length_cons, Fin.sum_univ_succ]
          simp only [cons_getD_zero, cons_getD_succ, Fin.val_succ, Nat.add_zero]
          rw [ih u h']
          simp [dotL]

/-- **桥 2（行列换位）**：列向量的 `getD` 等于逐行 `getD`。 -/
theorem getD_colL (rows : List (List ℤ)) (j i : Nat) :
    (colL rows j).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => cases i <;> rfl
  | cons r rs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [colL] using ih i

/-- **桥 3（组合系数）**：行取自列表的 `Fin` 索引加权和等于 `combL`。 -/
theorem sum_fin_rows_eq_combL (rows : List (List ℤ)) (w : List ℤ) (j : Nat)
    (h : rows.length = w.length) :
    (∑ i : Fin w.length, w.getD i.val 0 * (rows.getD i.val []).getD j 0)
      = combL rows w j := by
  have hlen : w.length = (colL rows j).length := by rw [colL, List.length_map, ← h]
  rw [combL, ← sum_fin_getD_mul w (colL rows j) hlen]
  exact Finset.sum_congr rfl (fun i _ => by rw [getD_colL])

/-- `Nat` 索引平移：`(k+1) + i = k + (i+1)`（`boxMinFrom` 递归步用）。 -/
theorem succ_add_eq_add_succ (k i : Nat) : (k + 1) + i = k + (i + 1) := by
  rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- **桥 4（盒下确界）**：`Fin` 索引的 `min` 求和等于 `boxMinFrom`。 -/
theorem sum_fin_boxMinFrom (lo hi : List ℤ) (rows : List (List ℤ)) (w : List ℤ) (k : Nat)
    (h : lo.length = hi.length) :
    (∑ j : Fin lo.length,
        min (combL rows w (k + j.val) * lo.getD j.val 0)
            (combL rows w (k + j.val) * hi.getD j.val 0))
      = boxMinFrom rows w lo hi k := by
  induction lo generalizing hi k with
  | nil =>
      cases hi with
      | nil => simp [boxMinFrom]
      | cons b u => simp at h
  | cons a t ih =>
      cases hi with
      | nil => simp at h
      | cons b u =>
          have h' : t.length = u.length := by simpa using h
          rw [List.length_cons, Fin.sum_univ_succ]
          simp only [cons_getD_zero, cons_getD_succ, Fin.val_succ, Nat.add_zero]
          rw [show (∑ i : Fin t.length,
                      min (combL rows w (k + (i.val + 1)) * t.getD i.val 0)
                          (combL rows w (k + (i.val + 1)) * u.getD i.val 0))
                  = (∑ i : Fin t.length,
                      min (combL rows w ((k + 1) + i.val) * t.getD i.val 0)
                          (combL rows w ((k + 1) + i.val) * u.getD i.val 0)) from
                Finset.sum_congr rfl (fun i _ => by rw [succ_add_eq_add_succ])]
          rw [ih u (k + 1) h']
          simp [boxMinFrom]

/-- **桥 4（盒下确界，`k = 0` 形式）**：样本模块直接使用这一形式（下标就是 `j.val`）。 -/
theorem sum_fin_boxMin (lo hi : List ℤ) (rows : List (List ℤ)) (w : List ℤ)
    (h : lo.length = hi.length) :
    (∑ j : Fin lo.length,
        min (combL rows w j.val * lo.getD j.val 0)
            (combL rows w j.val * hi.getD j.val 0))
      = boxMinL lo hi rows w := by
  rw [boxMinL, ← sum_fin_boxMinFrom lo hi rows w 0 h]
  exact Finset.sum_congr rfl (fun j _ => by simp)

/-! ## 端到端自检：2×2 小实例

这不是数学声明，只是在本模块内部验证「列表计算 + 四条桥 + 冻结 soundness」这条链路本身：
`rows = [[-1,0],[0,-1]]`、`rhs = [-2,-2]`、盒 `[0,1]²`、权重 `[1,1]` 有 `B = -4 < m = -2`；
权重全零时 `B = m = 0`，检查必须为假。 -/

namespace SelfTest

def loL : List ℤ := [0, 0]
def hiL : List ℤ := [1, 1]
def rowsL : List (List ℤ) := [[-1, 0], [0, -1]]
def rhsL : List ℤ := [-2, -2]
def wL : List ℤ := [1, 1]
def wZeroL : List ℤ := [0, 0]

/-- 由上述列表数据构造的 `Fin` 索引系统。 -/
def sys : LinearSystem (Fin 2) (Fin 2) where
  lo := fun j => loL.getD j.val 0
  hi := fun j => hiL.getD j.val 0
  lo_le_hi := by intro j; fin_cases j <;> decide
  rows := fun i j => (rowsL.getD i.val []).getD j.val 0
  rhs := fun i => rhsL.getD i.val 0

theorem checkL_true : checkL loL hiL rowsL rhsL wL = true := by decide
theorem checkL_zero_false : checkL loL hiL rowsL rhsL wZeroL = false := by decide

theorem combRhs_eq : combRhs sys (fun i : Fin 2 => wL.getD i.val 0) = dotL wL rhsL :=
  sum_fin_getD_mul wL rhsL (by decide)

theorem boxMin_eq : boxMin sys (fun i : Fin 2 => wL.getD i.val 0) = boxMinL loL hiL rowsL wL := by
  have hc : ∀ j : Fin 2, comb sys (fun i : Fin 2 => wL.getD i.val 0) j
      = combL rowsL wL j.val :=
    fun j => sum_fin_rows_eq_combL rowsL wL j.val (by decide)
  refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_))
    (sum_fin_boxMin loL hiL rowsL wL (by decide))
  rw [hc j]
  rfl

theorem check_eq : nonnegCheck sys (fun i : Fin 2 => wL.getD i.val 0)
    = checkL loL hiL rowsL rhsL wL := by
  unfold nonnegCheck checkL
  rw [combRhs_eq, boxMin_eq]

theorem check : nonnegCheck sys (fun i : Fin 2 => wL.getD i.val 0) = true := by
  rw [check_eq]; exact checkL_true

theorem empty : ∀ z, ¬ Feasible sys z :=
  nonnegCheck_sound sys _ (by intro i; fin_cases i <;> decide) check

end SelfTest

end Rho5.Shared.CertificateRules.ListCheck
