import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Algebraic infrastructure private to this bridge.
The Jacobian differentiates x,y,z (indices 0,1,2), never g (index 3).
The original package used the umbrella `import Mathlib`; X only carries a selective
fine-grained dependency cache, so the umbrella is replaced by exactly the modules this
file needs (MvPolynomial pderiv/eval, 3x3 matrix determinant notation, ℝ, `ring`).
Nothing else in the file changes. -/

noncomputable section
namespace Rho5.Algebraic

abbrev Poly := MvPolynomial (Fin 4) ℝ
abbrev Point := Fin 4 → ℝ
abbrev ev (v : Point) : Poly →+* ℝ := MvPolynomial.eval v

def point (x y z g : ℝ) : Point := ![x, y, z, g]
def xVar : Poly := MvPolynomial.X 0
def yVar : Poly := MvPolynomial.X 1
def zVar : Poly := MvPolynomial.X 2
def gVar : Poly := MvPolynomial.X 3

@[simp] theorem ev_xVar (v : Point) : ev v xVar = v 0 := by simp [xVar]
@[simp] theorem ev_yVar (v : Point) : ev v yVar = v 1 := by simp [yVar]
@[simp] theorem ev_zVar (v : Point) : ev v zVar = v 2 := by simp [zVar]
@[simp] theorem ev_gVar (v : Point) : ev v gVar = v 3 := by simp [gVar]

/-- Numeral literals in `Poly` are the images of `ℕ`-casts under `C`, so their formal
partial derivatives vanish.  This is only `MvPolynomial.pderiv_C` transported across the
`OfNat`/`Nat.cast` coercion; it adds no assumption, but it lets `simp` discharge the
`pderiv 0 (64 : Poly)`-shaped side conditions that the generated data files produce. -/
@[simp] theorem pderiv_natCast (i : Fin 4) (n : ℕ) :
    MvPolynomial.pderiv i ((n : Poly)) = 0 := by
  rw [← MvPolynomial.C_eq_coe_nat (R := ℝ) n, MvPolynomial.pderiv_C]

def det3 {R : Type*} [CommRing R]
    (a b c d e f h i j : R) : R :=
  a * (e * j - f * i) - b * (d * j - f * h) + c * (d * i - e * h)

theorem det3_eq_matrix_det {R : Type*} [CommRing R]
    (a b c d e f h i j : R) :
    det3 a b c d e f h i j = Matrix.det !![a,b,c;d,e,f;h,i,j] := by
  simp [det3, Matrix.det_fin_three] <;> ring

/-- The actual formal polynomial Jacobian determinant, with g held fixed. -/
def jacobianPoly (f₁ f₂ f₃ : Poly) : Poly :=
  det3 (MvPolynomial.pderiv 0 f₁) (MvPolynomial.pderiv 1 f₁)
    (MvPolynomial.pderiv 2 f₁)
    (MvPolynomial.pderiv 0 f₂) (MvPolynomial.pderiv 1 f₂)
    (MvPolynomial.pderiv 2 f₂)
    (MvPolynomial.pderiv 0 f₃) (MvPolynomial.pderiv 1 f₃)
    (MvPolynomial.pderiv 2 f₃)

theorem eval_jacobian_eq_det (v : Point) (f₁ f₂ f₃ : Poly) :
    ev v (jacobianPoly f₁ f₂ f₃) = Matrix.det
      !![ev v (MvPolynomial.pderiv 0 f₁),
         ev v (MvPolynomial.pderiv 1 f₁),
         ev v (MvPolynomial.pderiv 2 f₁);
         ev v (MvPolynomial.pderiv 0 f₂),
         ev v (MvPolynomial.pderiv 1 f₂),
         ev v (MvPolynomial.pderiv 2 f₂);
         ev v (MvPolynomial.pderiv 0 f₃),
         ev v (MvPolynomial.pderiv 1 f₃),
         ev v (MvPolynomial.pderiv 2 f₃)] := by
  simp [jacobianPoly, det3, Matrix.det_fin_three, map_add, map_mul, map_sub] <;> ring

structure CriticalAt (f₁ f₂ f₃ : Poly) (v : Point) : Prop where
  eq1 : ev v f₁ = 0
  eq2 : ev v f₂ = 0
  eq3 : ev v f₃ = 0
  jac : ev v (jacobianPoly f₁ f₂ f₃) = 0

/-- At a common zero, multiplying equations by factors multiplies the Jacobian
by their product. No statement is made away from the common zero. -/
theorem eval_jacobian_scale (v : Point) (f₁ f₂ f₃ a b c : Poly)
    (h₁ : ev v f₁ = 0) (h₂ : ev v f₂ = 0) (h₃ : ev v f₃ = 0) :
    ev v (jacobianPoly (a*f₁) (b*f₂) (c*f₃)) =
      (ev v a * ev v b * ev v c) * ev v (jacobianPoly f₁ f₂ f₃) := by
  simp only [jacobianPoly, det3, MvPolynomial.pderiv_mul, map_add, map_sub,
    map_mul, h₁, h₂, h₃, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem eval_jacobian_combo_first (v : Point) (f₁ f₂ f₃ a b c : Poly)
    (h₁ : ev v f₁ = 0) (h₂ : ev v f₂ = 0) (h₃ : ev v f₃ = 0) :
    ev v (jacobianPoly (a*f₁+b*f₂+c*f₃) f₂ f₃) =
      ev v a * ev v (jacobianPoly f₁ f₂ f₃) := by
  simp only [jacobianPoly, det3, MvPolynomial.pderiv_mul, map_add, map_sub,
    map_mul, h₁, h₂, h₃, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem eval_jacobian_combo_second (v : Point) (f₁ f₂ f₃ a b c : Poly)
    (h₁ : ev v f₁ = 0) (h₂ : ev v f₂ = 0) (h₃ : ev v f₃ = 0) :
    ev v (jacobianPoly f₁ (a*f₁+b*f₂+c*f₃) f₃) =
      ev v b * ev v (jacobianPoly f₁ f₂ f₃) := by
  simp only [jacobianPoly, det3, MvPolynomial.pderiv_mul, map_add, map_sub,
    map_mul, h₁, h₂, h₃, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem critical_replace_first (v : Point) (f₁ f₂ f₃ t s a b c : Poly)
    (hc : CriticalAt f₁ f₂ f₃ v) (hs : ev v s ≠ 0)
    (hid : s*t = a*f₁+b*f₂+c*f₃) : CriticalAt t f₂ f₃ v := by
  have hst : ev v s * ev v t = 0 := by
    have he := congrArg (fun f : Poly => ev v f) hid
    simpa only [map_add, map_mul, hc.eq1, hc.eq2, hc.eq3,
      mul_zero, add_zero] using he
  have ht : ev v t = 0 := (mul_eq_zero.mp hst).resolve_left hs
  have hj : ev v (jacobianPoly (s*t) f₂ f₃) = 0 := by
    rw [hid, eval_jacobian_combo_first v f₁ f₂ f₃ a b c
      hc.eq1 hc.eq2 hc.eq3, hc.jac, mul_zero]
  have hscale : ev v (jacobianPoly (s*t) f₂ f₃) =
      ev v s * ev v (jacobianPoly t f₂ f₃) := by
    simpa only [one_mul, map_one, mul_one] using
      eval_jacobian_scale v t f₂ f₃ s 1 1 ht hc.eq2 hc.eq3
  rw [hscale] at hj
  exact ⟨ht, hc.eq2, hc.eq3, (mul_eq_zero.mp hj).resolve_left hs⟩

theorem critical_replace_second (v : Point) (f₁ f₂ f₃ t s a b c : Poly)
    (hc : CriticalAt f₁ f₂ f₃ v) (hs : ev v s ≠ 0)
    (hid : s*t = a*f₁+b*f₂+c*f₃) : CriticalAt f₁ t f₃ v := by
  have hst : ev v s * ev v t = 0 := by
    have he := congrArg (fun f : Poly => ev v f) hid
    simpa only [map_add, map_mul, hc.eq1, hc.eq2, hc.eq3,
      mul_zero, add_zero] using he
  have ht : ev v t = 0 := (mul_eq_zero.mp hst).resolve_left hs
  have hj : ev v (jacobianPoly f₁ (s*t) f₃) = 0 := by
    rw [hid, eval_jacobian_combo_second v f₁ f₂ f₃ a b c
      hc.eq1 hc.eq2 hc.eq3, hc.jac, mul_zero]
  have hscale : ev v (jacobianPoly f₁ (s*t) f₃) =
      ev v s * ev v (jacobianPoly f₁ t f₃) := by
    simpa only [one_mul, map_one, mul_one] using
      eval_jacobian_scale v f₁ t f₃ 1 s 1 hc.eq1 ht hc.eq3
  rw [hscale] at hj
  exact ⟨hc.eq1, ht, hc.eq3, (mul_eq_zero.mp hj).resolve_left hs⟩

end Rho5.Algebraic
