import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Rho5.LocalAnalysis
noncomputable section
abbrev X := Fin 22 → ℝ
abbrev Y := Fin 21 → ℝ
abbrev coord (i : Fin 22) : X →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- Exact rational expression syntax; derivative semantics is proved recursively. -/
inductive Expr where
  | const : ℚ → Expr
  | var : Fin 22 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr

def Expr.eval : Expr → X → ℝ
  | .const c => fun _ => c
  | .var i => fun z => z i
  | .add a b => fun z => a.eval z + b.eval z
  | .mul a b => fun z => a.eval z * b.eval z
  | .neg a => fun z => -a.eval z

def Expr.differential : Expr → X → (X →L[ℝ] ℝ)
  | .const _ => fun _ => 0
  | .var i => fun _ => coord i
  | .add a b => fun z => a.differential z + b.differential z
  | .mul a b => fun z => a.eval z • b.differential z + b.eval z • a.differential z
  | .neg a => fun z => -a.differential z

theorem Expr.hasFDerivAt (a : Expr) (z : X) : HasFDerivAt a.eval (a.differential z) z := by
  induction a with
  | const c => exact hasFDerivAt_const (c : ℝ) z
  | var i => exact hasFDerivAt_apply i z
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg

/-- X22 order: k,r,w,A,B,c,d,p,e,beta,u0,u1,u2,x0,x1,x2,v0,v1,v2,q0,q1,q2. -/
def height (z : X) : ℝ := z 1 - z 2
def heldGuard (z : X) : ℝ := 1 + z 19 + z 9 * z 16 -- P0-
def releasedGuard (z : X) : ℝ := 1 - z 21 - z 9 * z 18 -- P2+
def consumed (z : X) : ℝ := 1 + z 2 + z 6 * z 4 + z 15 * z 21 + z 12 * z 18 -- O22-

def heightD : X →L[ℝ] ℝ := coord 1 - coord 2
def heldGuardD (z : X) : X →L[ℝ] ℝ := coord 19 + (z 9 • coord 16 + z 16 • coord 9)
def releasedGuardD (z : X) : X →L[ℝ] ℝ := -coord 21 - (z 9 • coord 18 + z 18 • coord 9)
def consumedD (z : X) : X →L[ℝ] ℝ := coord 2 +
  (z 6 • coord 4 + z 4 • coord 6) + (z 15 • coord 21 + z 21 • coord 15) +
  (z 12 • coord 18 + z 18 • coord 12)

theorem height_hasFDerivAt (z : X) : HasFDerivAt height heightD z :=
  (hasFDerivAt_apply 1 z).sub (hasFDerivAt_apply 2 z)
theorem heldGuard_hasFDerivAt (z : X) : HasFDerivAt heldGuard (heldGuardD z) z := by
  convert ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).add (hasFDerivAt_apply 19 z)).add
    ((hasFDerivAt_apply 9 z).mul (hasFDerivAt_apply 16 z)) using 1 <;>
    simp [heldGuard, heldGuardD]
theorem releasedGuard_hasFDerivAt (z : X) : HasFDerivAt releasedGuard (releasedGuardD z) z := by
  convert ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).sub (hasFDerivAt_apply 21 z)).sub
    ((hasFDerivAt_apply 9 z).mul (hasFDerivAt_apply 18 z)) using 1 <;>
    simp [releasedGuard, releasedGuardD]
theorem consumed_hasFDerivAt (z : X) : HasFDerivAt consumed (consumedD z) z := by
  convert (((((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).add (hasFDerivAt_apply 2 z)).add
    ((hasFDerivAt_apply 6 z).mul (hasFDerivAt_apply 4 z))).add
    ((hasFDerivAt_apply 15 z).mul (hasFDerivAt_apply 21 z))).add
    ((hasFDerivAt_apply 12 z).mul (hasFDerivAt_apply 18 z))) using 1 <;>
    simp [consumed, consumedD]

def cube (c : X) (ρ : ℝ) : Set X := {z | ∀ i, |z i - c i| ≤ ρ}

theorem cube_coord_abs {c z : X} {ρ : ℝ} (hz : z ∈ cube c ρ) (i : Fin 22) :
    |z i| ≤ |c i| + ρ := by
  have ht : |z i| ≤ |z i - c i| + |c i| := by
    simpa using abs_add_le (z i - c i) (c i)
  linarith [hz i]

/-- A genuine whole-box bound on the dual norm of the released P2+ derivative. -/
theorem releasedGuardD_bound {c z : X} {ρ : ℝ} (hz : z ∈ cube c ρ) (v : X) :
    |releasedGuardD z v| ≤ (1 + |c 9| + |c 18| + 2 * ρ) * ‖v‖ := by
  have hv (i : Fin 22) : |v i| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  have ht : |releasedGuardD z v| ≤ |v 21| + |z 9| * |v 18| + |z 18| * |v 9| := by
    simp only [releasedGuardD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coord,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    calc
      |-v 21 - (z 9 * v 18 + z 18 * v 9)| ≤ |v 21| + |z 9 * v 18 + z 18 * v 9| := by
        simpa only [abs_neg] using abs_sub (-v 21) (z 9 * v 18 + z 18 * v 9)
      _ ≤ |v 21| + |z 9 * v 18| + |z 18 * v 9| := by
        linarith [abs_add_le (z 9 * v 18) (z 18 * v 9)]
      _ = _ := by rw [abs_mul, abs_mul]
  have h9 := mul_le_mul_of_nonneg_left (hv 18) (abs_nonneg (z 9))
  have h18 := mul_le_mul_of_nonneg_left (hv 9) (abs_nonneg (z 18))
  have hcz9 := mul_le_mul_of_nonneg_right (cube_coord_abs hz 9) (norm_nonneg v)
  have hcz18 := mul_le_mul_of_nonneg_right (cube_coord_abs hz 18) (norm_nonneg v)
  nlinarith [hv 21]

/-- The exact quadratic Taylor remainder of this actual physical guard. -/
theorem releasedGuard_taylor (z d : X) :
    releasedGuard (z + d) = releasedGuard z + releasedGuardD z d - d 9 * d 18 := by
  simp [releasedGuard, releasedGuardD, coord]
  ring

/-- The guard survives an approximate inverse direction, once its signed
approximation estimate and the Neumann remainder have been established. -/
theorem releasedGuard_direction {c z v a : X} {ρ η m : ℝ}
    (hz : z ∈ cube c ρ) (herr : ‖v - a‖ ≤ η)
    (hg : 0 ≤ 1 + |c 9| + |c 18| + 2 * ρ)
    (ha : m + (1 + |c 9| + |c 18| + 2 * ρ) * η ≤ -releasedGuardD z a) :
    m ≤ releasedGuardD z (-v) := by
  have hb := releasedGuardD_bound hz (v - a)
  have hmul := mul_le_mul_of_nonneg_left herr hg
  rw [map_sub] at hb
  rw [map_neg]
  have hab := le_abs_self (releasedGuardD z v - releasedGuardD z a)
  linarith

end
end Rho5.LocalAnalysis
