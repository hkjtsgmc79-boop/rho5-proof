/-
D135 — 原论文 §8/S6 证书规则核（2/3）：有限实线性系统的精确检查器与 soundness
================================================================================

原论文 §8 的接受算术：对声明来源的必要行 `a_j · z ≤ b_j`（有限、整数系数，盒 `L ≤ z ≤ U`），
正确性非负整数权重给出

  `C = Σ_j w_j a_j`, `B = Σ_j w_j b_j`,  检查 `B − Σ_i min(C_i L_i, C_i U_i) < 0`。

`B − Σ min < 0` 排除**整个盒**中的实数可行赋值（不只是排除某个采样点）：
真实提升点必须属于这些必要行与盒，而组合后的行在盒上下确界上已经矛盾。

本文件给出：

* `LinearSystem`：整数系数的有限盒-行系统（盒非空是结构字段）；
* `comb`/`combRhs`/`boxMin`：上述 `C`、`B`、`m` 的精确整数定义；
* `nonnegCheck`：可判定的精确检查器（`decide`，纯内核整数算术，**不用** `native_decide`）；
* `nonneg_combination_sound` / `nonnegCheck_sound`：检查通过 ⟹ 无实数可行赋值（`check_sound`）；
* `interval_terminal_sound`：单表达式（区间）矛盾终端；
* `height_terminal_sound`：高度终端 `F = h·z`，`c = a − t·h`，`B − m ≤ t·α ⟹ F ≤ α`
  （只给安全界，**不**给不可行性）。

没有任何浮点、没有求解器、没有 `native_decide`：检查是整数比较，soundness 是纯代数。
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Basic
import Mathlib.Tactic.Push
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Rho5.Shared.CertificateRules

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **有限盒-行系统**（整数系数）：盒 `lo ≤ z ≤ hi`（要求 `lo ≤ hi`）与行
`Σ_j rows i j * z j ≤ rhs i`。原论文的实际终端都是这种形状（缩放后为整数）。 -/
structure LinearSystem (ι κ : Type*) [Fintype ι] [Fintype κ] where
  lo : κ → ℤ
  hi : κ → ℤ
  lo_le_hi : ∀ j, lo j ≤ hi j
  rows : ι → κ → ℤ
  rhs : ι → ℤ

/-- 非负组合后的坐标系数 `C j = Σ_i w i * rows i j`。 -/
def comb (S : LinearSystem ι κ) (w : ι → ℤ) (j : κ) : ℤ := ∑ i, w i * S.rows i j

/-- 非负组合后的右端 `B = Σ_i w i * rhs i`。 -/
def combRhs (S : LinearSystem ι κ) (w : ι → ℤ) : ℤ := ∑ i, w i * S.rhs i

/-- 盒在组合方向上的下确界 `m = Σ_j min (C_j lo_j) (C_j hi_j)`。
（`C_j ≥ 0` 时是 `C_j lo_j`，否则是 `C_j hi_j`，与原论文接受器一致。） -/
def boxMin (S : LinearSystem ι κ) (w : ι → ℤ) : ℤ :=
  ∑ j, min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)

/-- **精确检查器**：`B < m`。整数比较，可判定，无浮点。 -/
def nonnegCheck (S : LinearSystem ι κ) (w : ι → ℤ) : Bool := decide (combRhs S w < boxMin S w)

/-- `ℤ` 求和到 `ℚ` 的强制转换（本文件反复使用；`map_sum` 在 `Int.cast` 强制转换下不匹配）。 -/
@[simp] theorem intCast_sum {ι : Type*} [Fintype ι] (f : ι → ℤ) :
    ((∑ i, f i : ℤ) : ℚ) = ∑ i, (f i : ℚ) := by
  push_cast
  rfl

/-- 实数可行赋值：同时满足盒与全部声明行。 -/
def Feasible (S : LinearSystem ι κ) (z : κ → ℚ) : Prop :=
  (∀ j, (S.lo j : ℚ) ≤ z j ∧ z j ≤ (S.hi j : ℚ)) ∧
    ∀ i, (∑ j, (S.rows i j : ℚ) * z j) ≤ (S.rhs i : ℚ)

/-- `nonnegCheck = true` 的展开形式。 -/
theorem nonnegCheck_eq_true (S : LinearSystem ι κ) (w : ι → ℤ) :
    nonnegCheck S w = true ↔ combRhs S w < boxMin S w := by
  simp [nonnegCheck]

/-- **核心 soundness（非负组合终端）**：若 `B < m`，则盒内不存在满足全部行的实数赋值。
证明只用：行加权求和、盒在每个坐标上的 `min` 下界、以及 `B < m`。 -/
theorem nonneg_combination_sound (S : LinearSystem ι κ) (w : ι → ℤ)
    (hw : ∀ i, 0 ≤ w i) (hcheck : combRhs S w < boxMin S w) :
    ∀ z, ¬ Feasible S z := by
  intro z hz
  obtain ⟨hbox, hrows⟩ := hz
  -- (1) 加权行：Σ_j C_j z_j ≤ B
  have hswap : (∑ j, ((comb S w j : ℤ) : ℚ) * z j)
      = ∑ i, (w i : ℚ) * (∑ j, (S.rows i j : ℚ) * z j) := by
    simp only [comb]
    push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hkey1 : (∑ j, ((comb S w j : ℤ) : ℚ) * z j) ≤ ((combRhs S w : ℤ) : ℚ) := by
    rw [hswap]
    have : ((combRhs S w : ℤ) : ℚ) = ∑ i, (w i : ℚ) * (S.rhs i : ℚ) := by
      simp only [combRhs]
      push_cast
      rfl
    rw [this]
    exact Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (by exact_mod_cast hw i))
  -- (2) 盒下界：m ≤ Σ_j C_j z_j
  have hmin_le : ∀ j, ((min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j) : ℤ) : ℚ)
      ≤ ((comb S w j : ℤ) : ℚ) * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohi : S.lo j ≤ S.hi j := S.lo_le_hi j
    by_cases hc : (0 : ℤ) ≤ comb S w j
    · have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.lo j :=
        min_eq_left (mul_le_mul_of_nonneg_left hlohi hc)
      rw [h1]
      have hcQ : (0 : ℚ) ≤ ((comb S w j : ℤ) : ℚ) := by exact_mod_cast hc
      simpa only [Int.cast_mul] using mul_le_mul_of_nonneg_left hlo hcQ
    · have hc' : comb S w j < 0 := lt_of_not_ge hc
      have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.hi j :=
        min_eq_right (mul_le_mul_of_nonpos_left hlohi (le_of_lt hc'))
      rw [h1]
      have hcQ : ((comb S w j : ℤ) : ℚ) ≤ 0 := by exact_mod_cast le_of_lt hc'
      simpa only [Int.cast_mul] using mul_le_mul_of_nonpos_left hhi hcQ
  have hkey2 : ((boxMin S w : ℤ) : ℚ) ≤ ∑ j, ((comb S w j : ℤ) : ℚ) * z j := by
    rw [boxMin, intCast_sum]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  have hlt : ((combRhs S w : ℤ) : ℚ) < ((boxMin S w : ℤ) : ℚ) := by exact_mod_cast hcheck
  linarith

/-- **check_sound**：`nonnegCheck` 返回 `true` ⟹ 该有限行系统无实数可行赋值。
这是原论文接受器的实际可靠性接口：检查是精确整数算术，结论是盒上的全称否定。 -/
theorem nonnegCheck_sound (S : LinearSystem ι κ) (w : ι → ℤ) (hw : ∀ i, 0 ≤ w i)
    (h : nonnegCheck S w = true) : ∀ z, ¬ Feasible S z :=
  nonneg_combination_sound S w hw ((nonnegCheck_eq_true S w).mp h)

/-- 检查失败只说明该**证书**不成立，不说明系统可行（不声称反向）。 -/
theorem nonnegCheck_false_iff (S : LinearSystem ι κ) (w : ι → ℤ) :
    nonnegCheck S w = false ↔ ¬ combRhs S w < boxMin S w := by
  simp [nonnegCheck]

/-! ## 单表达式（区间）终端 -/

/-- **interval_terminal_sound**：一行 `a·z ≤ b` 与盒；若 `b < Σ_j min (a_j L_j) (a_j U_j)`，
则盒内不存在满足该行的实数点。这是非负组合规则在 `|ι| = 1`（单表达式）时的情形。 -/
theorem interval_terminal_sound {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (b : ℤ) (lo hi : κ → ℤ) (hlohi : ∀ j, lo j ≤ hi j)
    (hcheck : b < ∑ j, min (a j * lo j) (a j * hi j))
    (z : κ → ℚ) (hbox : ∀ j, (lo j : ℚ) ≤ z j ∧ z j ≤ (hi j : ℚ))
    (hrow : (∑ j, (a j : ℚ) * z j) ≤ (b : ℚ)) : False := by
  have hmin_le : ∀ j, ((min (a j * lo j) (a j * hi j) : ℤ) : ℚ) ≤ (a j : ℚ) * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    by_cases hc : (0 : ℤ) ≤ a j
    · have h1 : min (a j * lo j) (a j * hi j) = a j * lo j :=
        min_eq_left (mul_le_mul_of_nonneg_left (hlohi j) hc)
      rw [h1]
      have hcQ : (0 : ℚ) ≤ ((a j : ℤ) : ℚ) := by exact_mod_cast hc
      simpa only [Int.cast_mul] using mul_le_mul_of_nonneg_left hlo hcQ
    · have hc' : a j < 0 := lt_of_not_ge hc
      have h1 : min (a j * lo j) (a j * hi j) = a j * hi j :=
        min_eq_right (mul_le_mul_of_nonpos_left (hlohi j) (le_of_lt hc'))
      rw [h1]
      have hcQ : ((a j : ℤ) : ℚ) ≤ 0 := by exact_mod_cast le_of_lt hc'
      simpa only [Int.cast_mul] using mul_le_mul_of_nonpos_left hhi hcQ
  have h1 : ((∑ j, min (a j * lo j) (a j * hi j) : ℤ) : ℚ) ≤ ∑ j, (a j : ℚ) * z j := by
    rw [intCast_sum]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  have h3 : (b : ℚ) < ((∑ j, min (a j * lo j) (a j * hi j) : ℤ) : ℚ) := by
    exact_mod_cast hcheck
  linarith

/-! ## 高度终端（只给 α-安全，不给不可行） -/

/-- **height_terminal_sound**：设 `F = h·z`、`c = a − t·h`（`t > 0`），并已用非负组合得到
单一必要行 `a·z ≤ B`。若 `B − Σ_j min (c_j L_j) (c_j U_j) ≤ t·α`，则盒内每个满足该行的点
都有 `F z ≤ α`。这是 α-安全终端；它**不**排除 `F ≥ γ` 的点。 -/
theorem height_terminal_sound {κ : Type*} [Fintype κ]
    (a h : κ → ℚ) (B t α : ℚ) (lo hi : κ → ℚ) (hlohi : ∀ j, lo j ≤ hi j) (ht : 0 < t)
    (hcert : B - (∑ j, min ((a j - t * h j) * lo j) ((a j - t * h j) * hi j)) ≤ t * α)
    (z : κ → ℚ) (hbox : ∀ j, lo j ≤ z j ∧ z j ≤ hi j) (hrow : (∑ j, a j * z j) ≤ B) :
    (∑ j, h j * z j) ≤ α := by
  set c : κ → ℚ := fun j => a j - t * h j with hc
  have hmin : (∑ j, min (c j * lo j) (c j * hi j)) ≤ ∑ j, c j * z j := by
    apply Finset.sum_le_sum; intro j _
    obtain ⟨hlo, hhi⟩ := hbox j
    by_cases hcj : (0 : ℚ) ≤ c j
    · rw [min_eq_left (mul_le_mul_of_nonneg_left (hlohi j) hcj)]
      exact mul_le_mul_of_nonneg_left hlo hcj
    · have hcj' : c j < 0 := lt_of_not_ge hcj
      rw [min_eq_right (mul_le_mul_of_nonpos_left (hlohi j) (le_of_lt hcj'))]
      exact mul_le_mul_of_nonpos_left hhi (le_of_lt hcj')
  have hsplit : (∑ j, c j * z j) = (∑ j, a j * z j) - t * (∑ j, h j * z j) := by
    have h1 : (∑ j, c j * z j) = (∑ j, a j * z j) - ∑ j, (t * h j) * z j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; simp only [hc]; ring
    have h2 : (∑ j, (t * h j) * z j) = t * (∑ j, h j * z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, h2]
  have hmain : t * (∑ j, h j * z j) ≤ t * α := by linarith
  exact le_of_mul_le_mul_left hmain ht



/-! ## 有理系数版本（B16 实际终端的系数与右端是有理数） -/

namespace Rational

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **有理盒-行系统**：盒与行都是有理数（V31 的整数系统是它的特例）。 -/
structure RatSystem (ι κ : Type*) [Fintype ι] [Fintype κ] where
  lo : κ → ℚ
  hi : κ → ℚ
  lo_le_hi : ∀ j, lo j ≤ hi j
  rows : ι → κ → ℚ
  rhs : ι → ℚ

/-- 非负组合后的坐标系数 `C j = Σ_i w i * rows i j`。 -/
def comb (S : RatSystem ι κ) (w : ι → ℚ) (j : κ) : ℚ := ∑ i, w i * S.rows i j

/-- 非负组合后的右端 `B = Σ_i w i * rhs i`。 -/
def combRhs (S : RatSystem ι κ) (w : ι → ℚ) : ℚ := ∑ i, w i * S.rhs i

/-- 盒在组合方向上的下确界 `m = Σ_j min (C_j lo_j) (C_j hi_j)`。 -/
def boxMin (S : RatSystem ι κ) (w : ι → ℚ) : ℚ :=
  ∑ j, min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)

/-- **精确检查器**（有理数比较，可判定，无浮点）。 -/
def check (S : RatSystem ι κ) (w : ι → ℚ) : Bool := decide (combRhs S w < boxMin S w)

theorem check_eq_true (S : RatSystem ι κ) (w : ι → ℚ) :
    check S w = true ↔ combRhs S w < boxMin S w := by
  simp [check]

/-- 实数（有理）可行赋值。 -/
def Feasible (S : RatSystem ι κ) (z : κ → ℚ) : Prop :=
  (∀ j, S.lo j ≤ z j ∧ z j ≤ S.hi j) ∧ ∀ i, (∑ j, S.rows i j * z j) ≤ S.rhs i

/-- **soundness**：`B < m` ⟹ 盒内不存在满足全部行的有理赋值。 -/
theorem nonneg_combination_sound (S : RatSystem ι κ) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hcheck : combRhs S w < boxMin S w) :
    ∀ z, ¬ Feasible S z := by
  intro z hz
  obtain ⟨hbox, hrows⟩ := hz
  have hswap : (∑ j, comb S w j * z j) = ∑ i, w i * (∑ j, S.rows i j * z j) := by
    simp only [comb, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hkey1 : (∑ j, comb S w j * z j) ≤ combRhs S w := by
    rw [hswap]
    exact Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hw i))
  have hmin_le : ∀ j, min (comb S w j * S.lo j) (comb S w j * S.hi j) ≤ comb S w j * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohi : S.lo j ≤ S.hi j := S.lo_le_hi j
    by_cases hc : (0 : ℚ) ≤ comb S w j
    · rw [min_eq_left (mul_le_mul_of_nonneg_left hlohi hc)]
      exact mul_le_mul_of_nonneg_left hlo hc
    · have hc' : comb S w j < 0 := lt_of_not_ge hc
      rw [min_eq_right (mul_le_mul_of_nonpos_left hlohi (le_of_lt hc'))]
      exact mul_le_mul_of_nonpos_left hhi (le_of_lt hc')
  have hkey2 : boxMin S w ≤ ∑ j, comb S w j * z j := by
    rw [boxMin]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  linarith

/-- **check_sound**：有理检查器通过 ⟹ 该有限行系统无有理可行赋值。 -/
theorem check_sound (S : RatSystem ι κ) (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (h : check S w = true) : ∀ z, ¬ Feasible S z :=
  nonneg_combination_sound S w hw ((check_eq_true S w).mp h)

/-- 检查失败只说明该证书不成立（不声称反向）。 -/
theorem check_false_iff (S : RatSystem ι κ) (w : ι → ℚ) :
    check S w = false ↔ ¬ combRhs S w < boxMin S w := by
  simp [check]

end Rational

end Rho5.Shared.CertificateRules
