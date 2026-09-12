import Rho5.Algebraic.CriticalExistence.Interval
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
The generic R5 core uses the complete subtype of a closed cube. Coordinate
secants give the mean-value estimate by four exact telescoping steps. This is
stronger than bounding diagonal derivatives alone and does not invent a
single intermediate 4-by-4 Jacobian. No contraction on all of R^4 is assumed.
-/
namespace Rho5.Algebraic.CriticalExistence
noncomputable section
open Set

def Cube : Set Vec := {v | ∀ i, |v i| ≤ 1}

lemma cube_zero : (0 : Vec) ∈ Cube := by intro i; simp
lemma norm_le_one_of_cube {v : Vec} (h : v ∈ Cube) : ‖v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
  intro i; simpa only [Real.norm_eq_abs] using h i
lemma cube_isClosed : IsClosed Cube := by
  have h : Cube = ⋂ i : Fin 4, {v : Vec | |v i| ≤ (1:ℝ)} := by
    ext v; simp [Cube]
  rw [h]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const

/-- Four-term triangle inequality, grouped to match a left-nested sum on the right. -/
private lemma abs_sum_four_le (A B C D : ℝ) :
    |A+B+C+D| ≤ |A|+|B|+|C|+|D| := by
  have h1 : |(A+B)+C| ≤ |A+B| + |C| := abs_add_le _ _
  have h2 : |A+B| ≤ |A| + |B| := abs_add_le _ _
  have h3 : |(A+B)+C| ≤ |A| + |B| + |C| := h1.trans (add_le_add h2 (le_refl _))
  have h4 : |A+B+C+D| ≤ |(A+B)+C| + |D| := abs_add_le _ _
  calc |A+B+C+D| ≤ |(A+B)+C| + |D| := h4
    _ ≤ (|A| + |B| + |C|) + |D| := add_le_add h3 (le_refl _)
    _ = |A|+|B|+|C|+|D| := by ring

/-- Four coordinate changes stay in the same cube; their costs add to 1/4.
All endpoints used here are actual points of the cube. -/
theorem cube_lipschitz (f : Vec → Vec)
    (hstep : ∀ i j a b, a ∈ Cube → b ∈ Cube →
      (∀ k, k ≠ j → a k = b k) →
      |f b i - f a i| ≤ (1/16:ℝ) * |b j - a j|)
    {a b : Vec} (ha : a ∈ Cube) (hb : b ∈ Cube) :
    ‖f b - f a‖ ≤ (1/4:ℝ) * ‖b-a‖ := by
  let c1 : Vec := ![b 0, a 1, a 2, a 3]
  let c2 : Vec := ![b 0, b 1, a 2, a 3]
  let c3 : Vec := ![b 0, b 1, b 2, a 3]
  have h1 : c1 ∈ Cube := by
    intro i; fin_cases i <;> simp only [c1, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact hb 0
    · exact ha 1
    · exact ha 2
    · exact ha 3
  have h2 : c2 ∈ Cube := by
    intro i; fin_cases i <;> simp only [c2, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact hb 0
    · exact hb 1
    · exact ha 2
    · exact ha 3
  have h3 : c3 ∈ Cube := by
    intro i; fin_cases i <;> simp only [c3, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact ha 3
  have hn (i : Fin 4) : |b i-a i| ≤ ‖b-a‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (b-a) i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))).2
  intro i
  have h01 := hstep i 0 a c1 ha h1 (by
    intro k hk; fin_cases k <;> simp_all [c1])
  have h12 := hstep i 1 c1 c2 h1 h2 (by
    intro k hk; fin_cases k <;> simp_all [c1,c2])
  have h23 := hstep i 2 c2 c3 h2 h3 (by
    intro k hk; fin_cases k <;> simp_all [c2,c3])
  have h34 := hstep i 3 c3 b h3 hb (by
    intro k hk; fin_cases k <;> simp_all [c3])
  simp only [c1,c2,c3, Matrix.cons_val_zero, Matrix.cons_val_succ] at h01 h12 h23 h34
  have hsum : |f b i - f a i| ≤
      |f c1 i-f a i|+|f c2 i-f c1 i|+|f c3 i-f c2 i|+|f b i-f c3 i| := by
    -- Telescoping split, then the four-term triangle inequality.
    have hsplit : f b i - f a i =
        (f c1 i-f a i)+(f c2 i-f c1 i)+(f c3 i-f c2 i)+(f b i-f c3 i) := by ring
    rw [hsplit]
    simpa only [add_assoc] using
      abs_sum_four_le (f c1 i-f a i) (f c2 i-f c1 i) (f c3 i-f c2 i) (f b i-f c3 i)
  have hb0 := hn 0; have hb1 := hn 1; have hb2 := hn 2; have hb3 := hn 3
  -- Unfold the `let`-abbreviations everywhere so all the bounds below speak about
  -- the same syntactic points.
  dsimp only [c1, c2, c3] at hsum h01 h12 h23 h34 ⊢
  -- Each unit step costs at most (1/16)*‖b-a‖.
  have e1 : |f b i - f ![b 0, b 1, b 2, a 3] i| ≤ (1/16:ℝ)*‖b-a‖ :=
    h34.trans (mul_le_mul_of_nonneg_left hb3 (by norm_num))
  have e2 : |f ![b 0, b 1, b 2, a 3] i - f ![b 0, b 1, a 2, a 3] i| ≤ (1/16:ℝ)*‖b-a‖ := by
    refine (h23.trans (mul_le_mul_of_nonneg_left hb2 (by norm_num))).trans_eq ?_
    norm_num
  have e3 : |f ![b 0, b 1, a 2, a 3] i - f ![b 0, a 1, a 2, a 3] i| ≤ (1/16:ℝ)*‖b-a‖ := by
    refine (h12.trans (mul_le_mul_of_nonneg_left hb1 (by norm_num))).trans_eq ?_
    norm_num
  have e4 : |f ![b 0, a 1, a 2, a 3] i - f a i| ≤ (1/16:ℝ)*‖b-a‖ :=
    h01.trans (mul_le_mul_of_nonneg_left hb0 (by norm_num))
  change |f b i-f a i| ≤ (1/4:ℝ)*‖b-a‖
  linarith

theorem exists_unique_fixed_cube (f : Vec → Vec)
    (hstep : ∀ i j a b, a ∈ Cube → b ∈ Cube →
      (∀ k, k ≠ j → a k = b k) →
      |f b i-f a i| ≤ (1/16:ℝ)*|b j-a j|)
    (hcenter : ∀ i, |f 0 i| ≤ (1/2:ℝ)) :
    ∃! v : Vec, v ∈ Cube ∧ f v = v := by
  have hnorm {a b : Vec} (ha : a ∈ Cube) (hb : b ∈ Cube) :
      ‖f b - f a‖ ≤ (1/4:ℝ) * ‖b-a‖ := cube_lipschitz f hstep ha hb
  have hzero : ‖f 0‖ ≤ (1/2:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)).2
    intro i; simpa only [Real.norm_eq_abs] using hcenter i
  have hmaps : MapsTo f Cube Cube := by
    intro x hx
    have hdiff := hnorm cube_zero hx
    have hnx := norm_le_one_of_cube hx
    have htri : ‖f x‖ ≤ ‖f x-f 0‖+‖f 0‖ := by
      simpa using norm_add_le (f x-f 0) (f 0)
    have hnf : ‖f x‖ ≤ (3/4:ℝ) := by
      simp only [sub_zero] at hdiff; nlinarith
    intro i
    have hc : |f x i| ≤ ‖f x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f x) i
    linarith
  let S := {v : Vec // v ∈ Cube}
  letI : Nonempty S := ⟨⟨0,cube_zero⟩⟩
  letI : CompleteSpace S := cube_isClosed.isComplete.completeSpace_coe
  let g : S → S := fun x => ⟨f x.val, hmaps x.property⟩
  have hcont : ContractingWith (1/4 : NNReal) g := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa [g, dist_eq_norm] using hnorm y.property x.property
  let v : S := ContractingWith.fixedPoint g hcont
  have hv : g v = v := hcont.fixedPoint_isFixedPt
  refine ⟨v.val, ⟨v.property, congrArg Subtype.val hv⟩, ?_⟩
  intro w hw
  have hwfix : Function.IsFixedPt g (⟨w,hw.1⟩ : S) := Subtype.ext hw.2
  exact congrArg Subtype.val (hcont.fixedPoint_unique' hwfix hv)

def scale (m r : Vec) (u : Vec) : Vec := fun i => m i + r i*u i
def unscale (m r : Vec) (v : Vec) : Vec := fun i => (v i-m i)/r i

def CenteredBox (m r : Vec) (v : Vec) : Prop :=
  ∀ i, m i-r i ≤ v i ∧ v i ≤ m i+r i

lemma scale_unscale (m r v : Vec) (hr : ∀ i, 0 < r i) :
    scale m r (unscale m r v) = v := by
  funext i
  simp only [scale,unscale]
  field_simp [(hr i).ne']
  ring
lemma unscale_scale (m r u : Vec) (hr : ∀ i, 0 < r i) :
    unscale m r (scale m r u) = u := by
  funext i
  simp only [scale,unscale]
  field_simp [(hr i).ne']
  ring
lemma scale_zero (m r : Vec) : scale m r 0 = m := by funext i; simp [scale]
lemma scale_mem (m r u : Vec) (hr : ∀ i, 0 < r i) (hu : u ∈ Cube) :
    CenteredBox m r (scale m r u) := by
  intro i
  have hi := (abs_le.mp (hu i))
  dsimp [scale]
  constructor <;> nlinarith [hr i]
lemma unscale_mem (m r v : Vec) (hr : ∀ i, 0 < r i) (hv : CenteredBox m r v) :
    unscale m r v ∈ Cube := by
  intro i
  apply abs_le.mpr
  have hlo : -(1:ℝ) ≤ (v i - m i)/r i :=
    (le_div_iff₀ (hr i)).2 (by have hi := (hv i).1; simp only [unscale] at *; linarith)
  have hhi : (v i - m i)/r i ≤ 1 :=
    (div_le_iff₀ (hr i)).2 (by have hi := (hv i).2; simp only [unscale] at *; linarith)
  simpa only [unscale, Pi.neg_apply, Pi.one_apply, Real.norm_eq_abs] using ⟨hlo, hhi⟩

/-- Weighted-box R5 theorem. The hypotheses here are proved for concrete data
in `Instance`, rather than passed to the final project theorem. `C` is required
injective itself, not merely described as an approximate inverse. -/
theorem exists_unique_zero_of_interval_newton
    (F C : Vec → Vec) (T : Fin 4 → Expr) (m r : Vec)
    (hr : ∀ i, 0 < r i)
    (hnewton : ∀ v i, (T i).eval v = v i-C (F v) i)
    (hC0 : C 0 = 0) (hC : Function.Injective C)
    (hcenter : ∀ i, |(T i).eval m-m i| ≤ r i/2)
    (hslopes : ∀ i j a b, CenteredBox m r a → CenteredBox m r b →
      |(T i).secant j a b| * r j ≤ r i/16) :
    ∃! v : Vec, CenteredBox m r v ∧ F v = 0 := by
  let G : Vec → Vec := fun u i => ((T i).eval (scale m r u)-m i)/r i
  have hstep : ∀ i j a b, a ∈ Cube → b ∈ Cube →
      (∀ k, k ≠ j → a k=b k) →
      |G b i-G a i| ≤ (1/16:ℝ)*|b j-a j| := by
    intro i j a b ha hb heq
    let A := scale m r a
    let B := scale m r b
    have hA : CenteredBox m r A := scale_mem m r a hr ha
    have hB : CenteredBox m r B := scale_mem m r b hr hb
    have hdiff := (T i).sub_eq_secant j A B (by
      intro k hk; simp [A,B,scale,heq k hk])
    have hs := hslopes i j A B hA hB
    have hbd : |(T i).eval B-(T i).eval A| ≤ (r i/16)*|b j-a j| := by
      rw [hdiff,abs_mul]
      have he : B j-A j = r j*(b j-a j) := by dsimp [A,B,scale]; ring
      rw [he,abs_mul,abs_of_pos (hr j),←mul_assoc]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have he : G b i-G a i = ((T i).eval B-(T i).eval A)/r i := by
      dsimp [G,A,B]; ring
    rw [he,abs_div,abs_of_pos (hr i)]
    apply (div_le_iff₀ (hr i)).2
    nlinarith
  have hmid : ∀ i, |G 0 i| ≤ (1/2:ℝ) := by
    intro i
    dsimp [G]
    rw [scale_zero,abs_div,abs_of_pos (hr i)]
    apply (div_le_iff₀ (hr i)).2
    nlinarith [hcenter i]
  obtain ⟨u,hu,hunique⟩ := exists_unique_fixed_cube G hstep hmid
  have hroot : F (scale m r u) = 0 := by
    apply hC
    rw [hC0]
    funext i
    have hfix := congrFun hu.2 i
    change ((T i).eval (scale m r u)-m i)/r i = u i at hfix
    have he := (div_eq_iff (hr i).ne').mp hfix
    rw [hnewton] at he
    change C (F (scale m r u)) i = 0
    dsimp [scale] at he
    nlinarith
  refine ⟨scale m r u, ⟨scale_mem m r u hr hu.1,hroot⟩, ?_⟩
  intro v hv
  have hn : unscale m r v ∈ Cube := unscale_mem m r v hr hv.1
  have hf : G (unscale m r v) = unscale m r v := by
    funext i
    dsimp [G]
    rw [scale_unscale m r v hr,hnewton,hv.2,hC0]
    simp [unscale]
  have heq := hunique (unscale m r v) ⟨hn,hf⟩
  have heq' := congrArg (scale m r) heq
  simpa only [scale_unscale m r v hr] using heq'

end
end Rho5.Algebraic.CriticalExistence
