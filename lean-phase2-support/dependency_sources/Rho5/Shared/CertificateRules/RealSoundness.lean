/-
D135 — Stage B 叶模块（实数语义补足）：对任意 `ℝ` 赋值的精确检查器可靠性
==========================================================================

背景（见 `results/CERTIFICATE_RULES_SCOPE_CORRECTION.json`）：冻结的 `Linear.lean` 中
`Feasible`（整数系统）与 `Rational.Feasible`（有理系统）都把赋值量化在 `ℚ` 上，因此
`nonnegCheck_sound` / `Rational.check_sound` 只排除**有理**赋值；此前注释里「实数」的说法
比类型更宽。本模块**不修改**任何冻结文件，只在新叶里把同一论证在 `ℝ` 上重做一遍：

* `FeasibleR`（整数系数系统）与 `Rational.FeasibleR`（有理系数系统）：`z : κ → ℝ`，
  系数与盒端点强制转换为 `ℝ`；
* `nonneg_combination_sound_real` / `nonnegCheck_sound_real` 与
  `Rational.nonneg_combination_sound_real` / `Rational.check_sound_real`：
  **未改动**的精确检查器（同一个 `nonnegCheck`/`Rational.check`，同一个 `B < m`）
  加上非负权重，排除**所有** ℝ 赋值；
* `interval_terminal_sound_real`、`height_terminal_sound_real`：区间与高度终端的实数版
  （高度仍然只给 α **安全**，不给空性——两者语义保持分离）；
* `feasibleR_of_feasible`：有理可行点经强制转换给出实数可行点（故实数版结论更强，
  而不是由「有理无解」推出「实无解」）；
* `ratScale` / `feasible_of_ratScale` / `not_feasible_of_ratScale`：整数系统与按正因子
  `α,β` 缩放后的有理系统之间的**变量/行缩放与可行性搬运**（在 Lean 中证明），
  供 B16 的有理读法使用；权重的非负性经 `ratScaleWeights_nonneg` 搬运。

证明只做有限和、乘积、`min`、序与严格矛盾的搬运（`Finset` 归纳 + `push_cast` + `field_simp`），
没有稠密性、取整或「有理无解 ⟹ 实无解」之类的推理。
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Rho5.Shared.CertificateRules.Linear

namespace Rho5.Shared.CertificateRules

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## 强制转换引理（`ℤ`/`ℚ` → `ℝ`） -/

/-- `ℤ` 求和到 `ℝ` 的强制转换。 -/
theorem intCast_sumR (f : ι → ℤ) : ((∑ i, f i : ℤ) : ℝ) = ∑ i, (f i : ℝ) := by
  push_cast
  rfl

/-- `ℚ` 求和到 `ℝ` 的强制转换（`push_cast` 在 `Rat.cast` 下不触发，用 `Finset` 归纳）。 -/
theorem ratCast_sumR_aux (s : Finset ι) (f : ι → ℚ) :
    ((Finset.sum s f : ℚ) : ℝ) = Finset.sum s (fun i => (f i : ℝ)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rat.cast_add, ih]

theorem ratCast_sumR (f : ι → ℚ) : ((∑ i, f i : ℚ) : ℝ) = ∑ i, (f i : ℝ) :=
  ratCast_sumR_aux Finset.univ f

/-- `ℚ` 的 `min` 与强制转换交换。 -/
theorem ratCast_min (x y : ℚ) : ((min x y : ℚ) : ℝ) = min (x : ℝ) (y : ℝ) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]

/-- `ℤ` 的 `min` 与强制转换交换。 -/
theorem intCast_min (x y : ℤ) : ((min x y : ℤ) : ℝ) = min (x : ℝ) (y : ℝ) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]

/-! ## 整数系数系统的实数版可行性 -/

/-- **实数版可行性**（整数系数盒-行系统）：赋值 `z : κ → ℝ`，盒与行系数强制转换为 `ℝ`。 -/
def FeasibleR (S : LinearSystem ι κ) (z : κ → ℝ) : Prop :=
  (∀ j, (S.lo j : ℝ) ≤ z j ∧ z j ≤ (S.hi j : ℝ)) ∧
    ∀ i, (∑ j, (S.rows i j : ℝ) * z j) ≤ (S.rhs i : ℝ)

/-- 有理可行点经强制转换给出实数可行点：`FeasibleR` 强于 `Feasible`。 -/
theorem feasibleR_of_feasible (S : LinearSystem ι κ) (z : κ → ℚ) (hz : Feasible S z) :
    FeasibleR S (fun j => (z j : ℝ)) := by
  obtain ⟨hbox, hrows⟩ := hz
  refine ⟨fun j => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox j
    constructor
    · dsimp only
      exact_mod_cast h1
    · dsimp only
      exact_mod_cast h2
  · have hcast : ((∑ j, (S.rows i j : ℚ) * z j : ℚ) : ℝ)
        = ∑ j, (S.rows i j : ℝ) * (z j : ℝ) := by
      rw [ratCast_sumR]
      exact Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    rw [← hcast]
    exact_mod_cast hrows i

/-- **实数版核心 soundness（整数系数）**：`B < m` ⟹ 盒内不存在满足全部行的实数赋值。
与冻结的 `nonneg_combination_sound` 同构，只把 `ℚ` 换成 `ℝ`。 -/
theorem nonneg_combination_sound_real (S : LinearSystem ι κ) (w : ι → ℤ)
    (hw : ∀ i, 0 ≤ w i) (hcheck : combRhs S w < boxMin S w) :
    ∀ z : κ → ℝ, ¬ FeasibleR S z := by
  intro z hz
  obtain ⟨hbox, hrows⟩ := hz
  have hswap : (∑ j, ((comb S w j : ℤ) : ℝ) * z j)
      = ∑ i, (w i : ℝ) * (∑ j, (S.rows i j : ℝ) * z j) := by
    simp only [comb]
    have h1 : ∀ j, ((∑ i, w i * S.rows i j : ℤ) : ℝ)
        = ∑ i, (w i : ℝ) * (S.rows i j : ℝ) := by
      intro j
      rw [intCast_sumR]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; rfl)
    simp only [h1]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hkey1 : (∑ j, ((comb S w j : ℤ) : ℝ) * z j) ≤ ((combRhs S w : ℤ) : ℝ) := by
    rw [hswap]
    have : ((combRhs S w : ℤ) : ℝ) = ∑ i, (w i : ℝ) * (S.rhs i : ℝ) := by
      simp only [combRhs]
      rw [intCast_sumR]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; rfl)
    rw [this]
    exact Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (by exact_mod_cast hw i))
  have hmin_le : ∀ j, ((min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j) : ℤ) : ℝ)
      ≤ ((comb S w j : ℤ) : ℝ) * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohi : S.lo j ≤ S.hi j := S.lo_le_hi j
    by_cases hc : (0 : ℤ) ≤ comb S w j
    · have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.lo j :=
        min_eq_left (mul_le_mul_of_nonneg_left hlohi hc)
      rw [h1]
      have hcR : (0 : ℝ) ≤ ((comb S w j : ℤ) : ℝ) := by exact_mod_cast hc
      simpa only [Int.cast_mul] using mul_le_mul_of_nonneg_left hlo hcR
    · have hc' : comb S w j < 0 := lt_of_not_ge hc
      have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.hi j :=
        min_eq_right (mul_le_mul_of_nonpos_left hlohi (le_of_lt hc'))
      rw [h1]
      have hcR : ((comb S w j : ℤ) : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hc'
      simpa only [Int.cast_mul] using mul_le_mul_of_nonpos_left hhi hcR
  have hkey2 : ((boxMin S w : ℤ) : ℝ) ≤ ∑ j, ((comb S w j : ℤ) : ℝ) * z j := by
    rw [boxMin, intCast_sumR]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  have hlt : ((combRhs S w : ℤ) : ℝ) < ((boxMin S w : ℤ) : ℝ) := by exact_mod_cast hcheck
  linarith

/-- **实数版 check_sound（整数系数）**：未改动的 `nonnegCheck` 返回 `true` ⟹ 盒内不存在
满足全部行的**实数**赋值。 -/
theorem nonnegCheck_sound_real (S : LinearSystem ι κ) (w : ι → ℤ) (hw : ∀ i, 0 ≤ w i)
    (h : nonnegCheck S w = true) : ∀ z : κ → ℝ, ¬ FeasibleR S z :=
  nonneg_combination_sound_real S w hw ((nonnegCheck_eq_true S w).mp h)

/-- **实数版单表达式（区间）终端**：与冻结的 `interval_terminal_sound` 同形，赋值在 `ℝ` 上。 -/
theorem interval_terminal_sound_real {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (b : ℤ) (lo hi : κ → ℤ) (hlohi : ∀ j, lo j ≤ hi j)
    (hcheck : b < ∑ j, min (a j * lo j) (a j * hi j))
    (z : κ → ℝ) (hbox : ∀ j, (lo j : ℝ) ≤ z j ∧ z j ≤ (hi j : ℝ))
    (hrow : (∑ j, (a j : ℝ) * z j) ≤ (b : ℝ)) : False := by
  have hmin_le : ∀ j, ((min (a j * lo j) (a j * hi j) : ℤ) : ℝ) ≤ (a j : ℝ) * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohiR : (lo j : ℝ) ≤ (hi j : ℝ) := by exact_mod_cast hlohi j
    by_cases hc : (0 : ℤ) ≤ a j
    · have h1 : min (a j * lo j) (a j * hi j) = a j * lo j :=
        min_eq_left (mul_le_mul_of_nonneg_left (hlohi j) hc)
      rw [h1]
      have hcR : (0 : ℝ) ≤ (a j : ℝ) := by exact_mod_cast hc
      simpa only [Int.cast_mul] using mul_le_mul_of_nonneg_left hlo hcR
    · have hc' : a j < 0 := lt_of_not_ge hc
      have h1 : min (a j * lo j) (a j * hi j) = a j * hi j :=
        min_eq_right (mul_le_mul_of_nonpos_left (hlohi j) (le_of_lt hc'))
      rw [h1]
      have hcR : (a j : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hc'
      simpa only [Int.cast_mul] using mul_le_mul_of_nonpos_left hhi hcR
  have h1 : ((∑ j, min (a j * lo j) (a j * hi j) : ℤ) : ℝ) ≤ ∑ j, (a j : ℝ) * z j := by
    rw [intCast_sumR]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  have h3 : (b : ℝ) < ((∑ j, min (a j * lo j) (a j * hi j) : ℤ) : ℝ) := by
    exact_mod_cast hcheck
  linarith

/-- **实数版高度终端（只给 α 安全，不给空性）**：系数与证书保持 `ℚ`，赋值在 `ℝ` 上。
结论只是 `F ≤ α`；`F ≥ γ` 的点并未被排除（与空源语义严格分开）。 -/
theorem height_terminal_sound_real {κ : Type*} [Fintype κ]
    (a h : κ → ℚ) (B t α : ℚ) (lo hi : κ → ℚ) (hlohi : ∀ j, lo j ≤ hi j) (ht : 0 < t)
    (hcert : B - (∑ j, min ((a j - t * h j) * lo j) ((a j - t * h j) * hi j)) ≤ t * α)
    (z : κ → ℝ) (hbox : ∀ j, (lo j : ℝ) ≤ z j ∧ z j ≤ (hi j : ℝ))
    (hrow : (∑ j, (a j : ℝ) * z j) ≤ (B : ℝ)) :
    (∑ j, (h j : ℝ) * z j) ≤ (α : ℝ) := by
  set c : κ → ℚ := fun j => a j - t * h j with hcdef
  have hcertR : (B : ℝ) - (∑ j, min ((c j : ℝ) * (lo j : ℝ)) ((c j : ℝ) * (hi j : ℝ)))
      ≤ (t : ℝ) * (α : ℝ) := by
    have hcast : ((B - ∑ j, min (c j * lo j) (c j * hi j) : ℚ) : ℝ)
        = (B : ℝ) - ∑ j, min ((c j : ℝ) * (lo j : ℝ)) ((c j : ℝ) * (hi j : ℝ)) := by
      rw [Rat.cast_sub, ratCast_sumR]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [ratCast_min]; push_cast; ring)
    have htα : ((t * α : ℚ) : ℝ) = (t : ℝ) * (α : ℝ) := by push_cast; rfl
    rw [← hcast, ← htα]
    exact_mod_cast hcert
  have hmin : (∑ j, min ((c j : ℝ) * (lo j : ℝ)) ((c j : ℝ) * (hi j : ℝ)))
      ≤ ∑ j, (c j : ℝ) * z j := by
    apply Finset.sum_le_sum; intro j _
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohiR : (lo j : ℝ) ≤ (hi j : ℝ) := by exact_mod_cast hlohi j
    by_cases hcj : (0 : ℚ) ≤ c j
    · have hcjR : (0 : ℝ) ≤ (c j : ℝ) := by exact_mod_cast hcj
      rw [min_eq_left (mul_le_mul_of_nonneg_left hlohiR hcjR)]
      exact mul_le_mul_of_nonneg_left hlo hcjR
    · have hcj' : c j < 0 := lt_of_not_ge hcj
      have hcjR : (c j : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hcj'
      rw [min_eq_right (mul_le_mul_of_nonpos_left hlohiR hcjR)]
      exact mul_le_mul_of_nonpos_left hhi hcjR
  have hsplit : (∑ j, (c j : ℝ) * z j)
      = (∑ j, (a j : ℝ) * z j) - (t : ℝ) * (∑ j, (h j : ℝ) * z j) := by
    have h1 : (∑ j, (c j : ℝ) * z j)
        = (∑ j, (a j : ℝ) * z j) - ∑ j, ((t : ℝ) * (h j : ℝ)) * z j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp only [hcdef]; push_cast; ring
    have h2 : (∑ j, ((t : ℝ) * (h j : ℝ)) * z j) = (t : ℝ) * (∑ j, (h j : ℝ) * z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, h2]
  have hmain : (t : ℝ) * (∑ j, (h j : ℝ) * z j) ≤ (t : ℝ) * (α : ℝ) := by linarith
  exact le_of_mul_le_mul_left hmain (by exact_mod_cast ht)

/-! ## 正比例缩放：整数系统 ↔ 有理系统（Lean 内搬运） -/

/-- 由整数系统按正因子 `α`（盒）、`β`（行/右端）缩放得到的有理系统。 -/
def ratScale (S : LinearSystem ι κ) (α β : ℚ) (hα : 0 < α) : Rational.RatSystem ι κ where
  lo := fun j => (S.lo j : ℚ) / α
  hi := fun j => (S.hi j : ℚ) / α
  lo_le_hi := fun j => div_le_div_of_nonneg_right (by exact_mod_cast S.lo_le_hi j) (le_of_lt hα)
  rows := fun i j => (S.rows i j : ℚ) / β
  rhs := fun i => (S.rhs i : ℚ) / (α * β)

/-- 按正因子 `λ` 缩放后的有理权重。 -/
def ratScaleWeights (w : ι → ℤ) (lam : ℚ) : ι → ℚ := fun i => (w i : ℚ) / lam

/-- **可行性搬运**：缩放系统的有理可行点 `z` 对应整数系统的可行点 `fun j => α * z j`。
（只用到 `α,β > 0` 与有限和的重排，没有取整或稠密性假设。） -/
theorem feasible_of_ratScale (S : LinearSystem ι κ) (z : κ → ℚ) (α β : ℚ)
    (hα : 0 < α) (hβ : 0 < β) (h : Rational.Feasible (ratScale S α β hα) z) :
    Feasible S (fun j => α * z j) := by
  obtain ⟨hbox, hrows⟩ := h
  simp only [ratScale] at hbox hrows
  refine ⟨fun j => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox j
    exact ⟨by
        have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hα)
        rwa [mul_comm α ((S.lo j : ℚ) / α), div_mul_cancel₀ _ (ne_of_gt hα)] at h,
      by
        have h := mul_le_mul_of_nonneg_left h2 (le_of_lt hα)
        rwa [mul_comm α ((S.hi j : ℚ) / α), div_mul_cancel₀ _ (ne_of_gt hα)] at h⟩
  · have hmul := mul_le_mul_of_nonneg_left (hrows i) (le_of_lt (mul_pos hα hβ))
    rw [Finset.mul_sum] at hmul
    have hrhs : (α * β) * ((S.rhs i : ℚ) / (α * β)) = (S.rhs i : ℚ) := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (mul_pos hα hβ))]
    rw [hrhs] at hmul
    have hsum : (∑ j, (α * β) * (((S.rows i j : ℚ) / β) * z j))
        = ∑ j, (S.rows i j : ℚ) * (α * z j) :=
      Finset.sum_congr rfl (fun j _ => by field_simp [ne_of_gt hβ])
    rwa [hsum] at hmul

/-- 整数系统无有理可行点 ⟹ 缩放后的有理系统也无有理可行点。 -/
theorem not_feasible_ratScale (S : LinearSystem ι κ) (α β : ℚ) (hα : 0 < α) (hβ : 0 < β)
    (h : ∀ z : κ → ℚ, ¬ Feasible S z) :
    ∀ z : κ → ℚ, ¬ Rational.Feasible (ratScale S α β hα) z :=
  fun z hz => h _ (feasible_of_ratScale S z α β hα hβ hz)

/-- 权重的非负性在正比例缩放下保持。 -/
theorem ratScaleWeights_nonneg (w : ι → ℤ) (lam : ℚ) (hlam : 0 < lam) (hw : ∀ i, 0 ≤ w i) :
    ∀ i, 0 ≤ ratScaleWeights w lam i := by
  intro i
  simp only [ratScaleWeights]
  exact div_nonneg (by exact_mod_cast hw i) (le_of_lt hlam)

/-! ## 有理系数系统的实数版可行性 -/

namespace Rational

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **实数版可行性**（有理系数盒-行系统）：赋值 `z : κ → ℝ`，系数强制转换为 `ℝ`。 -/
def FeasibleR (S : RatSystem ι κ) (z : κ → ℝ) : Prop :=
  (∀ j, (S.lo j : ℝ) ≤ z j ∧ z j ≤ (S.hi j : ℝ)) ∧
    ∀ i, (∑ j, (S.rows i j : ℝ) * z j) ≤ (S.rhs i : ℝ)

/-- 有理可行点经强制转换给出实数可行点。 -/
theorem feasibleR_of_feasible (S : RatSystem ι κ) (z : κ → ℚ) (hz : Feasible S z) :
    FeasibleR S (fun j => (z j : ℝ)) := by
  obtain ⟨hbox, hrows⟩ := hz
  refine ⟨fun j => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox j
    constructor
    · dsimp only
      exact_mod_cast h1
    · dsimp only
      exact_mod_cast h2
  · have hcast : ((∑ j, S.rows i j * z j : ℚ) : ℝ)
        = ∑ j, (S.rows i j : ℝ) * (z j : ℝ) := by
      rw [ratCast_sumR]
      exact Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    rw [← hcast]
    exact_mod_cast hrows i

/-- **实数版核心 soundness（有理系数）**：`B < m` ⟹ 盒内不存在满足全部行的实数赋值。 -/
theorem nonneg_combination_sound_real (S : RatSystem ι κ) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hcheck : combRhs S w < boxMin S w) :
    ∀ z : κ → ℝ, ¬ FeasibleR S z := by
  intro z hz
  obtain ⟨hbox, hrows⟩ := hz
  have hswap : (∑ j, ((comb S w j : ℚ) : ℝ) * z j)
      = ∑ i, ((w i : ℚ) : ℝ) * (∑ j, ((S.rows i j : ℚ) : ℝ) * z j) := by
    simp only [comb]
    have h1 : ∀ j, ((∑ i, w i * S.rows i j : ℚ) : ℝ)
        = ∑ i, ((w i : ℚ) : ℝ) * ((S.rows i j : ℚ) : ℝ) := by
      intro j
      rw [ratCast_sumR]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; rfl)
    simp only [h1]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hkey1 : (∑ j, ((comb S w j : ℚ) : ℝ) * z j) ≤ ((combRhs S w : ℚ) : ℝ) := by
    rw [hswap]
    have : ((combRhs S w : ℚ) : ℝ) = ∑ i, ((w i : ℚ) : ℝ) * ((S.rhs i : ℚ) : ℝ) := by
      simp only [combRhs]
      rw [ratCast_sumR]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; rfl)
    rw [this]
    exact Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (by exact_mod_cast hw i))
  have hmin_le : ∀ j, ((min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j) : ℚ) : ℝ)
      ≤ ((comb S w j : ℚ) : ℝ) * z j := by
    intro j
    obtain ⟨hlo, hhi⟩ := hbox j
    have hlohi : S.lo j ≤ S.hi j := S.lo_le_hi j
    by_cases hc : (0 : ℚ) ≤ comb S w j
    · have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.lo j :=
        min_eq_left (mul_le_mul_of_nonneg_left hlohi hc)
      rw [h1]
      have hcR : (0 : ℝ) ≤ ((comb S w j : ℚ) : ℝ) := by exact_mod_cast hc
      simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left hlo hcR
    · have hc' : comb S w j < 0 := lt_of_not_ge hc
      have h1 : min ((comb S w j) * S.lo j) ((comb S w j) * S.hi j)
          = (comb S w j) * S.hi j :=
        min_eq_right (mul_le_mul_of_nonpos_left hlohi (le_of_lt hc'))
      rw [h1]
      have hcR : ((comb S w j : ℚ) : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hc'
      simpa only [Rat.cast_mul] using mul_le_mul_of_nonpos_left hhi hcR
  have hkey2 : ((boxMin S w : ℚ) : ℝ) ≤ ∑ j, ((comb S w j : ℚ) : ℝ) * z j := by
    rw [boxMin, ratCast_sumR]
    exact Finset.sum_le_sum (fun j _ => hmin_le j)
  have hlt : ((combRhs S w : ℚ) : ℝ) < ((boxMin S w : ℚ) : ℝ) := by exact_mod_cast hcheck
  linarith

/-- **实数版 check_sound（有理系数）**：未改动的 `Rational.check` 返回 `true` ⟹ 盒内不存在
满足全部行的**实数**赋值。 -/
theorem check_sound_real (S : RatSystem ι κ) (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (h : check S w = true) : ∀ z : κ → ℝ, ¬ FeasibleR S z :=
  nonneg_combination_sound_real S w hw ((check_eq_true S w).mp h)

end Rational

/-- **实数版可行性搬运**：缩放系统的实数可行点 `z` 对应整数系统的实数可行点 `α·z`。
（与有理版同一代数，只多一步 `ℚ → ℝ` 的除法强制转换。） -/
theorem feasibleR_of_ratScale (S : LinearSystem ι κ) (z : κ → ℝ) (α β : ℚ)
    (hα : 0 < α) (hβ : 0 < β) (h : Rational.FeasibleR (ratScale S α β hα) z) :
    FeasibleR S (fun j => (α : ℝ) * z j) := by
  obtain ⟨hbox, hrows⟩ := h
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hαne : (α : ℝ) ≠ 0 := ne_of_gt hαR
  have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβR
  have hαβne : (α : ℝ) * (β : ℝ) ≠ 0 := mul_ne_zero hαne hβne
  simp only [ratScale] at hbox hrows
  refine ⟨fun j => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox j
    constructor
    · have hkey : (α : ℝ) * (((S.lo j : ℚ) / α : ℚ) : ℝ) = (S.lo j : ℝ) := by
        rw [Rat.cast_div]
        push_cast
        field_simp [hαne]
      have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt hαR)
      rwa [hkey] at hh
    · have hkey : (α : ℝ) * (((S.hi j : ℚ) / α : ℚ) : ℝ) = (S.hi j : ℝ) := by
        rw [Rat.cast_div]
        push_cast
        field_simp [hαne]
      have hh := mul_le_mul_of_nonneg_left h2 (le_of_lt hαR)
      rwa [hkey] at hh
  · have hmul := mul_le_mul_of_nonneg_left (hrows i) (le_of_lt (mul_pos hαR hβR))
    rw [Finset.mul_sum] at hmul
    have hrhs : (α : ℝ) * (β : ℝ) * (((S.rhs i : ℚ) / (α * β) : ℚ) : ℝ) = (S.rhs i : ℝ) := by
      rw [Rat.cast_div]
      push_cast
      field_simp [hαβne]
    rw [hrhs] at hmul
    have hsum : (∑ j, (α : ℝ) * (β : ℝ) * ((((S.rows i j : ℚ) / β : ℚ) : ℝ) * z j))
        = ∑ j, (S.rows i j : ℝ) * ((α : ℝ) * z j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Rat.cast_div]
      push_cast
      field_simp [hαne, hβne]
    rwa [hsum] at hmul


end Rho5.Shared.CertificateRules
