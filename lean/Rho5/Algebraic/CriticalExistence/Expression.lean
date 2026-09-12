import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
G04/R5 polynomial circuits. `secant` is a divided-difference circuit, NOT a
claim that all coordinates share one mean-value point. Its diagonal is the
actual formal and analytic partial derivative. The fourth equation is a
3-by-3 determinant; differentiating this circuit has four directions.
-/
namespace Rho5.Algebraic.CriticalExistence
noncomputable section
abbrev Vec := Fin 4 → ℝ
inductive Expr where
  | rat : ℚ → Expr
  | var : Fin 4 → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr

def Expr.eval (v : Vec) : Expr → ℝ
  | .rat q => (q : ℝ)
  | .var i => v i
  | .add a b => a.eval v + b.eval v
  | .neg a => -a.eval v
  | .mul a b => a.eval v * b.eval v

def Expr.partial (i : Fin 4) : Expr → Expr
  | .rat _ => .rat 0
  | .var j => .rat (if j = i then 1 else 0)
  | .add a b => .add (a.partial i) (b.partial i)
  | .neg a => .neg (a.partial i)
  | .mul a b => .add (.mul (a.partial i) b) (.mul a (b.partial i))

def Expr.poly : Expr → MvPolynomial (Fin 4) ℝ
  | .rat q => MvPolynomial.C (q : ℝ)
  | .var i => MvPolynomial.X i
  | .add a b => a.poly + b.poly
  | .neg a => -a.poly
  | .mul a b => a.poly * b.poly

@[simp] theorem Expr.eval_poly (e : Expr) (v : Vec) :
    MvPolynomial.eval v e.poly = e.eval v := by
  induction e <;> simp_all [Expr.poly, Expr.eval]

@[simp] theorem Expr.poly_partial (e : Expr) (i : Fin 4) :
    (e.partial i).poly = MvPolynomial.pderiv i e.poly := by
  induction e with
  | rat q => simp [Expr.partial, Expr.poly]
  | var j =>
    by_cases h : j = i
    · subst j; simp [Expr.partial, Expr.poly]
    · simp [Expr.partial, Expr.poly, h, MvPolynomial.pderiv_X_of_ne h]
  | add a b ha hb => simp [Expr.partial, Expr.poly, ha, hb, map_add]
  | neg a ha => simp [Expr.partial, Expr.poly, ha, map_neg]
  | mul a b ha hb =>
    -- `simp only` (rather than `simp`) keeps the two summands of the Leibniz rule
    -- in a canonical order and closes the goal directly.
    simp only [Expr.partial, Expr.poly, ha, hb, map_add, MvPolynomial.pderiv_mul]

/-- At two endpoints, different factors may be evaluated at different endpoints.
This recurrence is exact and its interval extension is also a derivative bound. -/
def Expr.secant (i : Fin 4) (v w : Vec) : Expr → ℝ
  | .rat _ => 0
  | .var j => if j = i then 1 else 0
  | .add a b => a.secant i v w + b.secant i v w
  | .neg a => -a.secant i v w
  | .mul a b => a.secant i v w * b.eval w + a.eval v * b.secant i v w

@[simp] theorem Expr.secant_diag (e : Expr) (i : Fin 4) (v : Vec) :
    e.secant i v v = (e.partial i).eval v := by
  induction e with
  | rat q => simp [Expr.secant,Expr.partial,Expr.eval]
  | var j => by_cases h : j=i <;> simp [Expr.secant,Expr.partial,Expr.eval,h]
  | add a b ha hb => simp [Expr.secant,Expr.partial,Expr.eval,ha,hb]
  | neg a ha => simp [Expr.secant,Expr.partial,Expr.eval,ha]
  | mul a b ha hb => simp [Expr.secant,Expr.partial,Expr.eval,ha,hb]

/-- Exact single-coordinate mean-value identity, including a zero coordinate
increment. No division and no existential common intermediate point. -/
theorem Expr.sub_eq_secant (e : Expr) (i : Fin 4) (v w : Vec)
    (h : ∀ j, j ≠ i → v j = w j) :
    e.eval w - e.eval v = e.secant i v w * (w i - v i) := by
  induction e with
  | rat q => simp [Expr.eval, Expr.secant]
  | var j =>
    by_cases hj : j = i
    · subst j; simp [Expr.eval, Expr.secant]
    · simp [Expr.eval, Expr.secant, hj, h j hj]
  | add a b ha hb => simp only [Expr.eval, Expr.secant]; linarith
  | neg a ha => simp only [Expr.eval, Expr.secant]; linarith
  | mul a b ha hb =>
    simp only [Expr.eval, Expr.secant]
    calc
      a.eval w * b.eval w - a.eval v * b.eval v =
          (a.eval w - a.eval v) * b.eval w +
            a.eval v * (b.eval w - b.eval v) := by ring
      _ = _ := by rw [ha, hb]; ring

private theorem update_self (v : Vec) (i : Fin 4) :
    Function.update v i (v i) = v := by
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

/-- The same diagonal slopes really are ordinary real partial derivatives.
This is a chain-rule proof, not a symbolic-only assertion. -/
theorem Expr.hasDerivAt_update (e : Expr) (i : Fin 4) (v : Vec) :
    HasDerivAt (fun t : ℝ => e.eval (Function.update v i t))
      (e.secant i v v) (v i) := by
  induction e with
  | rat q => simpa [Expr.eval, Expr.secant] using hasDerivAt_const (v i) (q : ℝ)
  | var j =>
    by_cases h : j = i
    · subst j
      simpa [Expr.eval, Expr.secant] using hasDerivAt_id (v i)
    · simpa [Expr.eval, Expr.secant, Function.update, h] using
        hasDerivAt_const (v i) (v j)
  | add a b ha hb => simpa only [Expr.eval, Expr.secant] using ha.add hb
  | neg a ha => simpa only [Expr.eval, Expr.secant] using ha.neg
  | mul a b ha hb =>
    simpa only [Expr.eval, Expr.secant, update_self] using ha.mul hb

/-- The displayed 3-by-3 determinant as an unexpanded arithmetic circuit. -/
def detExpr (a b c d e f h i j : Expr) : Expr :=
  .add
    (.add (.mul a (.add (.mul e j) (.neg (.mul f i))))
      (.neg (.mul b (.add (.mul d j) (.neg (.mul f h))))))
    (.mul c (.add (.mul d i) (.neg (.mul e h))))

end
end Rho5.Algebraic.CriticalExistence
