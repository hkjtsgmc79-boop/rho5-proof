import Rho5.Algebraic.CandidateBox

noncomputable section
namespace Rho5.Algebraic

/-- Cancel only factors whose nonvanishing has already been obtained from the box.
The determinant here is still the determinant of the original three equations. -/
theorem original_to_reduced (v : Point) (hguard : GuardAt v)
    (hc : CriticalAt p1Poly p2Poly p3Poly v) :
    CriticalAt n1Poly n2Poly n3Poly v := by
  have hn1prod : ev v factor1 * ev v n1Poly = 0 := by
    simpa only [p1_factor, map_mul] using hc.eq1
  have hn2prod : ev v factor2 * ev v n2Poly = 0 := by
    simpa only [p2_factor, map_mul] using hc.eq2
  have hn3prod : ev v factor3 * ev v n3Poly = 0 := by
    simpa only [p3_factor, map_mul] using hc.eq3
  have hn1 : ev v n1Poly = 0 :=
    (mul_eq_zero.mp hn1prod).resolve_left (factor1_ne v hguard)
  have hn2 : ev v n2Poly = 0 :=
    (mul_eq_zero.mp hn2prod).resolve_left (factor2_ne v hguard)
  have hn3 : ev v n3Poly = 0 :=
    (mul_eq_zero.mp hn3prod).resolve_left (factor3_ne v hguard)
  have hj := hc.jac
  rw [p1_factor, p2_factor, p3_factor,
    eval_jacobian_scale v n1Poly n2Poly n3Poly factor1 factor2 factor3
      hn1 hn2 hn3] at hj
  have hprod : ev v factor1 * ev v factor2 * ev v factor3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (factor1_ne v hguard) (factor2_ne v hguard))
      (factor3_ne v hguard)
  exact ⟨hn1, hn2, hn3, (mul_eq_zero.mp hj).resolve_left hprod⟩

/-- Three concrete polynomial row replacements give a triangular critical system.
No hypothesis asserting the selected factor or its derivative is supplied. -/
theorem reduced_to_triangular (v : Point) (hguard : GuardAt v)
    (hc : CriticalAt n1Poly n2Poly n3Poly v) :
    CriticalAt elimX elimP n3Poly v := by
  have h₁ : CriticalAt elimX n2Poly n3Poly v :=
    critical_replace_first v n1Poly n2Poly n3Poly elimX scale1
      yDen (-(yDen*zVar)) (-(yVar*cancelR*qY))
      hc (scale1_ne v hguard) first_elimination
  have h₂ : CriticalAt elimX reducedG n3Poly v :=
    critical_replace_second v elimX n2Poly n3Poly reducedG scale2
      0 (yDen^3) (-multiplierY)
      h₁ (scale2_ne v hguard) second_elimination
  exact critical_replace_second v elimX reducedG n3Poly elimP scale3
    (-multiplierX) (xDen^5) 0
    h₂ (scale3_ne v hguard) third_elimination

/-- This is the previously missing critical-point-to-repeated-root implication. -/
theorem candidate_system_implies_elimP_and_derivative
    (x y z g : ℝ) (hb : CandidateBox x y z g)
    (h1 : P1 x y z g = 0) (h2 : P2 x y z g = 0)
    (h3 : P3 x y z g = 0) (hJ : J x y z g = 0) :
    ev (point x y z g) elimP = 0 ∧
    ev (point x y z g) elimDP = 0 := by
  let v := point x y z g
  have hguard : GuardAt v := guards_of_box hb
  have hc : CriticalAt p1Poly p2Poly p3Poly v := ⟨h1,h2,h3,hJ⟩
  have ht := reduced_to_triangular v hguard (original_to_reduced v hguard hc)
  have hj := ht.jac
  rw [triangular_jacobian, map_mul] at hj
  exact ⟨ht.eq2, (mul_eq_zero.mp hj).resolve_left (triangular_multiplier_ne v hguard)⟩

end Rho5.Algebraic
