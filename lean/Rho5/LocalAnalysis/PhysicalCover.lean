import Rho5.LocalAnalysis.SampleData
import Mathlib.Tactic.FinCases

/-! Finite exact partition of the frozen 100 physical source expressions.
The 78 whole-box positivity inequalities remain an explicit separate interface. -/
namespace Rho5.LocalAnalysis.V43
noncomputable section
open Rho5.LocalAnalysis
set_option maxRecDepth 10000
def activeIndex : Fin 21 → Fin 100 := ![0, 6, 8, 26, 28, 30, 34, 46, 47, 49, 51, 57, 63, 67, 73, 17, 82, 83, 87, 94, 95]
def inactiveIndex : Fin 78 → Fin 100 := ![1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 48, 50, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 64, 65, 66, 68, 69, 70, 71, 72, 74, 76, 77, 78, 79, 80, 81, 84, 85, 86, 88, 89, 90, 91, 92, 93, 96, 97, 98, 99]
def inactiveLabels : Fin 78 → String := !["e-", "beta+", "beta-", "head+", "head-", "u0-", "x0-", "v0+", "v0-", "q0+", "q0-", "L0+", "L0-", "P0+", "D00-", "S00+", "S00-", "O00+", "O00-", "D01+", "D01-", "S01+", "O01+", "D02+", "S02+", "S02-", "O02+", "u1+", "u1-", "x1+", "x1-", "v1+", "v1-", "q1+", "q1-", "L1+", "L1-", "P1+", "D10-", "S10-", "O10-", "D11+", "D11-", "S11+", "S11-", "O11-", "D12+", "D12-", "S12+", "S12-", "O12-", "u2+", "u2-", "x2-", "v2+", "v2-", "q2+", "q2-", "L2-", "P2-", "D20+", "D20-", "S20+", "S20-", "O20+", "D21-", "S21+", "S21-", "O21-", "D22+", "D22-", "S22+", "S22-", "O22+", "r-w", "positive_p", "positive_k", "positive_r"]
def inactiveExpr (i : Fin 78) : Expr := physicalExpr (inactiveIndex i)
def releasedIndex : Fin 100 := 75
def coverTag : Fin 100 → Sum (Fin 21) (Sum (Fin 78) Unit) := ![
  .inl 0,
  .inr (.inl 0),
  .inr (.inl 1),
  .inr (.inl 2),
  .inr (.inl 3),
  .inr (.inl 4),
  .inl 1,
  .inr (.inl 5),
  .inl 2,
  .inr (.inl 6),
  .inr (.inl 7),
  .inr (.inl 8),
  .inr (.inl 9),
  .inr (.inl 10),
  .inr (.inl 11),
  .inr (.inl 12),
  .inr (.inl 13),
  .inl 15,
  .inr (.inl 14),
  .inr (.inl 15),
  .inr (.inl 16),
  .inr (.inl 17),
  .inr (.inl 18),
  .inr (.inl 19),
  .inr (.inl 20),
  .inr (.inl 21),
  .inl 3,
  .inr (.inl 22),
  .inl 4,
  .inr (.inl 23),
  .inl 5,
  .inr (.inl 24),
  .inr (.inl 25),
  .inr (.inl 26),
  .inl 6,
  .inr (.inl 27),
  .inr (.inl 28),
  .inr (.inl 29),
  .inr (.inl 30),
  .inr (.inl 31),
  .inr (.inl 32),
  .inr (.inl 33),
  .inr (.inl 34),
  .inr (.inl 35),
  .inr (.inl 36),
  .inr (.inl 37),
  .inl 7,
  .inl 8,
  .inr (.inl 38),
  .inl 9,
  .inr (.inl 39),
  .inl 10,
  .inr (.inl 40),
  .inr (.inl 41),
  .inr (.inl 42),
  .inr (.inl 43),
  .inr (.inl 44),
  .inl 11,
  .inr (.inl 45),
  .inr (.inl 46),
  .inr (.inl 47),
  .inr (.inl 48),
  .inr (.inl 49),
  .inl 12,
  .inr (.inl 50),
  .inr (.inl 51),
  .inr (.inl 52),
  .inl 13,
  .inr (.inl 53),
  .inr (.inl 54),
  .inr (.inl 55),
  .inr (.inl 56),
  .inr (.inl 57),
  .inl 14,
  .inr (.inl 58),
  .inr (.inr ()),
  .inr (.inl 59),
  .inr (.inl 60),
  .inr (.inl 61),
  .inr (.inl 62),
  .inr (.inl 63),
  .inr (.inl 64),
  .inl 16,
  .inl 17,
  .inr (.inl 65),
  .inr (.inl 66),
  .inr (.inl 67),
  .inl 18,
  .inr (.inl 68),
  .inr (.inl 69),
  .inr (.inl 70),
  .inr (.inl 71),
  .inr (.inl 72),
  .inr (.inl 73),
  .inl 19,
  .inl 20,
  .inr (.inl 74),
  .inr (.inl 75),
  .inr (.inl 76),
  .inr (.inl 77)]
theorem active_index_exact (i : Fin 21) : physicalExpr (activeIndex i) = activeExpr i := by
  fin_cases i <;> rfl

theorem released_index_exact : physicalExpr releasedIndex = releasedExpr := rfl

theorem physical_partition (i : Fin 100) : physicalExpr i =
    match coverTag i with
    | .inl j => activeExpr j
    | .inr (.inl j) => inactiveExpr j
    | .inr (.inr _) => releasedExpr := by
  fin_cases i <;> rfl

/-- Actual polynomial physical subset, with strict pivot-domain qualification. -/
def Physical (z : X) : Prop :=
  (∀ i, 0 ≤ (physicalExpr i).eval z) ∧ 0 < z 0 ∧ 0 < z 1 ∧ 0 < z 7

def InactiveBox : Prop := ∀ z ∈ cube center radius, ∀ i,
  (1 / 200 : ℝ) < (inactiveExpr i).eval z

theorem Physical.chart_nonneg {z : X} (hz : Physical z) (i : Fin 21) : 0 ≤ chart z i := by
  have h := hz.1 (activeIndex i)
  rw [active_index_exact] at h
  exact h

theorem Physical.released_nonneg {z : X} (hz : Physical z) : 0 ≤ releasedGuard z := by
  have h := hz.1 releasedIndex
  rw [released_index_exact, releasedExpr_meaning] at h
  exact h

theorem physical_of_chart (z : X) (hchart : ∀ i, 0 ≤ chart z i)
    (hrel : 0 ≤ releasedGuard z)
    (hinactive : ∀ i, (1 / 200 : ℝ) < (inactiveExpr i).eval z) : Physical z := by
  have hp : 0 < z 7 := by
    have h := hinactive 75
    have he : inactiveExpr 75 = .mul (.const (1 / 1)) (.var 7) := rfl
    rw [he] at h
    norm_num [Expr.eval] at h
    linarith
  have hk : 0 < z 0 := by
    have h := hinactive 76
    have he : inactiveExpr 76 = .mul (.const (1 / 1)) (.var 0) := rfl
    rw [he] at h
    norm_num [Expr.eval] at h
    linarith
  have hr : 0 < z 1 := by
    have h := hinactive 77
    have he : inactiveExpr 77 = .mul (.const (1 / 1)) (.var 1) := rfl
    rw [he] at h
    norm_num [Expr.eval] at h
    linarith
  refine ⟨?_, hk, hr, hp⟩
  intro i
  rw [physical_partition]
  cases coverTag i with
  | inl j => exact hchart j
  | inr tag =>
    cases tag with
    | inl j => exact le_trans (by norm_num) (hinactive j).le
    | inr _ => simpa only [releasedExpr_meaning] using hrel

end
end Rho5.LocalAnalysis.V43
