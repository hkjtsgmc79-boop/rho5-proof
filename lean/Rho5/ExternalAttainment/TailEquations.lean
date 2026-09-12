import Rho5.ExternalAttainment.SchurIdentities

noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-- Compact polynomial numerators, used to avoid a huge rational expansion.
They are proved equal to the original `n1Poly/n2Poly` with their exact extra z. -/
def halfNumerator (x y z : ℝ) : ℝ :=
  2 * denomT x y z + z*(z-1)*(y+1)

def bottomNumerator (x y z : ℝ) : ℝ :=
  (y+z^2)*denomR x y z + y*(x*z+z^2+z-1)*denomT x y z

def cornerNumerator (x y z : ℝ) : ℝ :=
  2*(x+1)-z*(x+z)^2

def numeratorOne (x y z : ℝ) : ℝ :=
  y*(-corePivot x y z)*denomR x y z*halfNumerator x y z
  - y*(-corePivot x y z)*denomT x y z*denomR x y z*corePivot x y z
  + coreArm x y z*bottomNumerator x y z*denomT x y z

def numeratorTwo (x y z : ℝ) : ℝ :=
  y*(x+1)*denomR x y z*halfNumerator x y z
  - y*denomT x y z*denomR x y z*cornerNumerator x y z
  - (x+1)*denomT x y z*bottomNumerator x y z

/-- Crucially, the reduced R7 numerator is z times the input n1, not n1. -/
theorem n1_polynomial_bridge (x y z g : ℝ) :
    z * Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n1Poly =
      numeratorOne x y z := by
  simp [Rho5.Algebraic.n1Poly, Rho5.Algebraic.point,
    numeratorOne, halfNumerator, bottomNumerator, corePivot, coreArm,
    denomR, denomT, map_add, map_sub, map_mul, map_pow] <;> ring

theorem n2_polynomial_bridge (x y z g : ℝ) :
    z * Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n2Poly =
      numeratorTwo x y z := by
  simp [Rho5.Algebraic.n2Poly, Rho5.Algebraic.point,
    numeratorTwo, halfNumerator, bottomNumerator, cornerNumerator,
    denomR, denomT, map_add, map_sub, map_mul, map_pow] <;> ring

variable {x y z g : ℝ}

theorem original_roots_reduced
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n1Poly = 0 ∧
    Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n2Poly = 0 ∧
    Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n3Poly = 0 := by
  let v := Rho5.Algebraic.point x y z g
  have hg : Rho5.Algebraic.GuardAt v := Rho5.Algebraic.guards_of_box box
  have h1m : Rho5.Algebraic.ev v Rho5.Algebraic.factor1 *
      Rho5.Algebraic.ev v Rho5.Algebraic.n1Poly = 0 := by
    rw [← map_mul, ← Rho5.Algebraic.p1_factor]
    exact h1
  have h2m : Rho5.Algebraic.ev v Rho5.Algebraic.factor2 *
      Rho5.Algebraic.ev v Rho5.Algebraic.n2Poly = 0 := by
    rw [← map_mul, ← Rho5.Algebraic.p2_factor]
    exact h2
  have h3m : Rho5.Algebraic.ev v Rho5.Algebraic.factor3 *
      Rho5.Algebraic.ev v Rho5.Algebraic.n3Poly = 0 := by
    rw [← map_mul, ← Rho5.Algebraic.p3_factor]
    exact h3
  exact ⟨(mul_eq_zero.mp h1m).resolve_left (Rho5.Algebraic.factor1_ne v hg),
    (mul_eq_zero.mp h2m).resolve_left (Rho5.Algebraic.factor2_ne v hg),
    (mul_eq_zero.mp h3m).resolve_left (Rho5.Algebraic.factor3_ne v hg)⟩

/-- All rational identities below retain their real, nonzero denominators. -/
theorem residualOne_identity (box : Rho5.Algebraic.CandidateBox x y z g) :
    (halfHeight x y z - corePivot x y z
        - coreBottom x y z * coreArm x y z / corePivot x y z) *
      (y*(-corePivot x y z)*denomT x y z*denomR x y z) =
      numeratorOne x y z := by
  dsimp only [halfHeight, coreBottom, coreArm, headEntry,
    numeratorOne, halfNumerator, bottomNumerator]
  field_simp [y_ne box, corePivot_ne box, denomT_ne box, denomR_ne box] <;> ring

theorem residualTwo_identity (box : Rho5.Algebraic.CandidateBox x y z g) :
    (halfHeight x y z - (coreCorner x y z + coreBottom x y z)) *
      (y*(x+1)*denomT x y z*denomR x y z) = numeratorTwo x y z := by
  dsimp only [halfHeight, coreCorner, coreBottom, headEntry,
    numeratorTwo, halfNumerator, bottomNumerator, cornerNumerator]
  field_simp [y_ne box, x_add_one_ne box, denomT_ne box, denomR_ne box] <;> ring

theorem residualThree_identity (box : Rho5.Algebraic.CandidateBox x y z g) :
    denomT x y z * (g - 2*halfHeight x y z) =
      Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n3Poly := by
  have he : Rho5.Algebraic.ev (Rho5.Algebraic.point x y z g) Rho5.Algebraic.n3Poly =
      (g-4)*denomT x y z - 2*z*(z-1)*(y+1) := by
    simp [Rho5.Algebraic.n3Poly, Rho5.Algebraic.cancelD, Rho5.Algebraic.yDen,
      Rho5.Algebraic.point,
      denomT, map_add, map_sub, map_mul, map_pow] <;> ring
  rw [he]
  dsimp only [halfHeight]
  field_simp [denomT_ne box] <;> ring

/-- Original P1/P2/P3 imply all four exact tail relations; J is not needed. -/
theorem tail_relations
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    stageH x y z g 0 0 + stageH x y z g 1 0 = 0 ∧
    stageH x y z g 0 0 - stageH x y z g 1 1 = 0 ∧
    g - 2*stageH x y z g 0 0 = 0 ∧
    stageH x y z g 0 0 = stageH x y z g 0 1 := by
  obtain ⟨hn1, hn2, hn3⟩ := original_roots_reduced box h1 h2 h3
  have hn1' : numeratorOne x y z = 0 := by
    rw [← n1_polynomial_bridge x y z g, hn1, mul_zero]
  have hn2' : numeratorTwo x y z = 0 := by
    rw [← n2_polynomial_bridge x y z g, hn2, mul_zero]
  have hd1 : y*(-corePivot x y z)*denomT x y z*denomR x y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero
      (mul_ne_zero (y_ne box) (neg_ne_zero.mpr (corePivot_ne box)))
      (denomT_ne box)) (denomR_ne box)
  have hd2 : y*(x+1)*denomT x y z*denomR x y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (y_ne box) (x_add_one_ne box))
      (denomT_ne box)) (denomR_ne box)
  have he1 := residualOne_identity box
  rw [hn1'] at he1
  have hz1 := (mul_eq_zero.mp he1).resolve_right hd1
  have he2 := residualTwo_identity box
  rw [hn2'] at he2
  have hz2 := (mul_eq_zero.mp he2).resolve_right hd2
  have he3 := residualThree_identity box
  rw [hn3] at he3
  have hz3 := (mul_eq_zero.mp he3).resolve_left (denomT_ne box)
  simp only [stageH_eq box]
  change halfHeight x y z +
      (-corePivot x y z - coreBottom x y z*coreArm x y z/corePivot x y z) = 0 ∧
    halfHeight x y z - (coreCorner x y z + coreBottom x y z) = 0 ∧
    g - 2*halfHeight x y z = 0 ∧ halfHeight x y z = halfHeight x y z
  exact ⟨by linarith [hz1], hz2, hz3, rfl⟩

def targetTail (g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![g/2, g/2; -(g/2), g/2]

theorem stageH_eq_targetTail
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    stageH x y z g = targetTail g := by
  obtain ⟨h10, h11, hg, h01⟩ := tail_relations box h1 h2 h3
  ext i j
  fin_cases i <;> fin_cases j
  · change stageH x y z g 0 0 = g/2
    linarith
  · change stageH x y z g 0 1 = g/2
    linarith
  · change stageH x y z g 1 0 = -(g/2)
    linarith
  · change stageH x y z g 1 1 = g/2
    linarith

theorem stageH_eq_smul
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    stageH x y z g = (g/2) • (!![(1:ℝ), 1; -1, 1]) := by
  rw [stageH_eq_targetTail box h1 h2 h3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [targetTail] <;> ring

theorem stageL_00
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    stageL x y z g 0 0 = g := by
  have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0:ℝ)<4) (candidate_g_gt_four box))
  rw [stageL, stageH_eq_targetTail box h1 h2 h3]
  change g/2 - (-(g/2))*(g/2)/(g/2) = g
  field_simp [hg] <;> ring

end Rho5.ExternalAttainment
