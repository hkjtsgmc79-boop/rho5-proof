import Rho5.Certificate.B24MinorBridge.Witness
import Rho5.ExternalBFibreCapacity.FiniteBounds

/-!
The only source predicate exposed to the caller is `NormalizedB`.  The internal
named coordinates below are a transparent re-encoding of that predicate; they do
not contain feasibility, maximum, or path conclusions as data fields.
-/
namespace Rho5.ExternalBFibreCapacity

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24MinorBridge (Qualified)

noncomputable section

/-- Exactly seventeen real coordinates.  In particular `q` is actual q. -/
@[ext] structure Frame where
  k : ℝ
  A : ℝ
  B : ℝ
  c : ℝ
  d : ℝ
  u : Fin 3 → ℝ
  x : Fin 3 → ℝ
  v : Fin 3 → ℝ
  q : Fin 3 → ℝ

structure Tail where
  r : ℝ
  s : ℝ
  t : ℝ

def tailHeight (t : Tail) : ℝ := t.r + t.s * t.t / t.r

/-- A raw encoding.  The last coordinate is *computed*, never independent. -/
def encode (f : Frame) (beta p e : ℝ) (t : Tail) : Point :=
  ![f.k, t.r, t.s, t.t, f.A, f.B, f.c, f.d, p, e, beta,
    f.u 0, f.u 1, f.u 2, f.x 0, f.x 1, f.x 2,
    f.v 0, f.v 1, f.v 2, f.q 0, f.q 1, f.q 2, tailHeight t]

def frameOf (z : Point) : Frame :=
  ⟨z 0, z 4, z 5, z 6, z 7,
    ![z 11, z 12, z 13], ![z 14, z 15, z 16],
    ![z 17, z 18, z 19], ![z 20, z 21, z 22]⟩

def tailOf (z : Point) : Tail := ⟨z 1, z 2, z 3⟩

def frameVector (f : Frame) : Fin 17 → ℝ :=
  ![f.k, f.A, f.B, f.c, f.d, f.u 0, f.u 1, f.u 2,
    f.x 0, f.x 1, f.x 2, f.v 0, f.v 1, f.v 2, f.q 0, f.q 1, f.q 2]

def frameOfVector (v : Fin 17 → ℝ) : Frame :=
  ⟨v 0,v 1,v 2,v 3,v 4,![v 5,v 6,v 7],![v 8,v 9,v 10],
    ![v 11,v 12,v 13],![v 14,v 15,v 16]⟩

@[simp] theorem frameOfVector_frameVector (f : Frame) :
    frameOfVector (frameVector f) = f := by
  apply Frame.ext <;> try rfl
  all_goals
    funext i
    fin_cases i <;> rfl

@[simp] theorem frameVector_frameOfVector (v : Fin 17 → ℝ) :
    frameVector (frameOfVector v) = v := by
  funext i
  fin_cases i <;> rfl

/-- The source assumptions of the task, and no high-value or sign-chart assumptions. -/
def NormalizedB (z : Point) : Prop :=
  Qualified z ∧ 1 ≤ z 8 ∧ 0 ≤ z 9 ∧ 0 ≤ z 10

/-- The actual core, with the frozen B16 multiplication order. -/
def core (f : Frame) (t : Tail) : Fin 3 → Fin 3 → ℝ :=
  ![![f.k, f.A, f.B],
    ![f.k * f.c, t.r + f.A * f.c, t.s + f.B * f.c],
    ![f.k * f.d, t.t + f.A * f.d, -t.r + f.B * f.d]]

def stage (f : Frame) (t : Tail) (i j : Fin 3) : ℝ :=
  core f t i j + f.x i * f.q j

def original (f : Frame) (t : Tail) (i j : Fin 3) : ℝ :=
  core f t i j + f.u i * f.v j + f.x i * f.q j

structure FrameBounds (f : Frame) : Prop where
  k_pos : 0 < f.k
  u_bound : ∀ i, |f.u i| ≤ 1
  x_bound : ∀ i, |f.x i| ≤ 1
  v_bound : ∀ i, |f.v i| ≤ 1

/-- Original head, all six prefix bands, and actual q-stage bounds. -/
structure PrefixBounds (f : Frame) (beta p e : ℝ) : Prop where
  one_le_p : 1 ≤ p
  e_nonneg : 0 ≤ e
  e_le_one : e ≤ 1
  beta_nonneg : 0 ≤ beta
  beta_le_one : beta ≤ 1
  head : |p - e * beta| ≤ 1
  left : ∀ i, |p * f.x i - e * f.u i| ≤ 1
  right : ∀ j, |beta * f.v j + f.q j| ≤ 1
  q_stage : ∀ j, |f.q j| ≤ p

/-- All nine cells of every layer, plus the positive CP tail. -/
structure TailBounds (f : Frame) (p : ℝ) (t : Tail) : Prop where
  r_pos : 0 < t.r
  s_nonneg : 0 ≤ t.s
  s_le_r : t.s ≤ t.r
  t_nonneg : 0 ≤ t.t
  t_le_r : t.t ≤ t.r
  core : ∀ i j, |core f t i j| ≤ f.k
  stage : ∀ i j, |stage f t i j| ≤ p
  original : ∀ i j, |original f t i j| ≤ 1

def Admissible (f : Frame) (beta p e : ℝ) (t : Tail) : Prop :=
  FrameBounds f ∧ PrefixBounds f beta p e ∧ TailBounds f p t

@[simp] theorem u_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.u (encode f b p e t) i = f.u i := by
  fin_cases i <;> rfl
@[simp] theorem x_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.xv (encode f b p e t) i = f.x i := by
  fin_cases i <;> rfl
@[simp] theorem v_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.v (encode f b p e t) i = f.v i := by
  fin_cases i <;> rfl
@[simp] theorem q_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.q (encode f b p e t) i = f.q i := by
  fin_cases i <;> rfl
@[simp] theorem D_encode (f : Frame) (b p e : ℝ) (t : Tail) (i j : Fin 3) :
    Rho5.Certificate.B16.D (encode f b p e t) i j = core f t i j := by
  fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem S_encode (f : Frame) (b p e : ℝ) (t : Tail) (i j : Fin 3) :
    Rho5.Certificate.B16.S (encode f b p e t) i j = stage f t i j := by
  simp [Rho5.Certificate.B16.S, stage]
@[simp] theorem O_encode (f : Frame) (b p e : ℝ) (t : Tail) (i j : Fin 3) :
    Rho5.Certificate.B16.O (encode f b p e t) i j = original f t i j := by
  simp [Rho5.Certificate.B16.O, original]
@[simp] theorem L_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.L (encode f b p e t) i = p * f.x i - e * f.u i := by
  change p * Rho5.Certificate.B16.xv (encode f b p e t) i -
    e * Rho5.Certificate.B16.u (encode f b p e t) i = _
  rw [x_encode, u_encode]
@[simp] theorem P_encode (f : Frame) (b p e : ℝ) (t : Tail) (i : Fin 3) :
    Rho5.Certificate.B16.P (encode f b p e t) i = b * f.v i + f.q i := by
  change b * Rho5.Certificate.B16.v (encode f b p e t) i +
    Rho5.Certificate.B16.q (encode f b p e t) i = _
  rw [v_encode, q_encode]

@[simp] theorem frameOf_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    frameOf (encode f b p e t) = f := by
  apply Frame.ext <;> try rfl
  all_goals
    funext i
    fin_cases i <;> rfl

@[simp] theorem tailOf_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    tailOf (encode f b p e t) = t := by cases t; rfl

/-- No inverse Schur assumptions occur in this conversion. -/
theorem admissible_iff_normalized (f : Frame) (b p e : ℝ) (t : Tail) :
    Admissible f b p e t ↔ NormalizedB (encode f b p e t) := by
  constructor
  · rintro ⟨hf, hp, ht⟩
    refine ⟨?_, hp.one_le_p, hp.e_nonneg, hp.beta_nonneg⟩
    refine {
      physical := {
        d_bound := ?_, o_bound := ?_, s_bound := ?_, l_bound := ?_,
        p_bound := ?_, q_bound := ?_, r_pos := ht.r_pos,
        height := rfl, order_t := ht.t_le_r }
      headBand := {
        abs_e := ?_, abs_beta := ?_, abs_u := ?_, abs_x := ?_, abs_v := ?_,
        abs_p_sub_e_mul_beta := ?_, abs_L := ?_ }
      p_pos := ?_, k_pos := hf.k_pos,
      s_nonneg := ht.s_nonneg, s_le_r := ht.s_le_r, t_nonneg := ht.t_nonneg }
    · simpa only [D_encode] using ht.core
    · simpa only [O_encode] using ht.original
    · simpa only [S_encode] using ht.stage
    · simpa only [L_encode] using hp.left
    · simpa only [P_encode] using hp.right
    · simpa only [q_encode] using hp.q_stage
    · change |e| ≤ 1
      rw [abs_of_nonneg hp.e_nonneg]; exact hp.e_le_one
    · change |b| ≤ 1
      rw [abs_of_nonneg hp.beta_nonneg]; exact hp.beta_le_one
    · simpa only [u_encode] using hf.u_bound
    · simpa only [Rho5.Certificate.B24Reconstruction.x, x_encode] using hf.x_bound
    · simpa only [v_encode] using hf.v_bound
    · change |p-e*b| ≤ 1
      exact hp.head
    · change ∀ i, |p * Rho5.Certificate.B16.xv (encode f b p e t) i -
          e * Rho5.Certificate.B16.u (encode f b p e t) i| ≤ 1
      simpa only [u_encode, x_encode] using hp.left
    · change 0 < p
      linarith [hp.one_le_p]
  · rintro ⟨h, hp, he, hb⟩
    have he1 : e ≤ 1 := by
      have hx := h.headBand.abs_e
      change |e| ≤ 1 at hx
      exact (abs_le.mp hx).2
    have hb1 : b ≤ 1 := by
      have hx := h.headBand.abs_beta
      change |b| ≤ 1 at hx
      exact (abs_le.mp hx).2
    refine ⟨⟨h.k_pos, ?_, ?_, ?_⟩,
      ⟨hp, he, he1, hb, hb1, ?_, ?_, ?_, ?_⟩,
      ⟨h.physical.r_pos, h.s_nonneg, h.s_le_r, h.t_nonneg,
        h.physical.order_t, ?_, ?_, ?_⟩⟩
    · simpa only [u_encode] using h.headBand.abs_u
    · simpa only [Rho5.Certificate.B24Reconstruction.x, x_encode] using h.headBand.abs_x
    · simpa only [v_encode] using h.headBand.abs_v
    · exact h.headBand.abs_p_sub_e_mul_beta
    · simpa only [L_encode] using h.physical.l_bound
    · simpa only [P_encode] using h.physical.p_bound
    · simpa only [q_encode] using h.physical.q_bound
    · simpa only [D_encode] using h.physical.d_bound
    · simpa only [S_encode] using h.physical.s_bound
    · simpa only [O_encode] using h.physical.o_bound

/-- Exact decoding uses only the original physical height equation. -/
theorem encode_decode (z : Point) (h : Rho5.Certificate.B16.Physical z) :
    encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := by
  funext i
  fin_cases i <;> try rfl
  exact h.height.symm

theorem admissible_decode (z : Point) (h : NormalizedB z) :
    Admissible (frameOf z) (z 10) (z 8) (z 9) (tailOf z) := by
  apply (admissible_iff_normalized _ _ _ _ _).mpr
  simpa only [encode_decode z h.1.physical] using h

theorem tailBounds_mono_p {f : Frame} {p P : ℝ} {t : Tail}
    (h : TailBounds f p t) (hp : p ≤ P) : TailBounds f P t := by
  exact { h with stage := fun i j => (h.stage i j).trans hp }

def tailMix (a b : Tail) (lam : ℝ) : Tail :=
  ⟨mix a.r b.r lam, mix a.s b.s lam, mix a.t b.t lam⟩

@[simp] theorem tailMix_zero (a b : Tail) : tailMix a b 0 = a := by
  cases a; cases b; simp [tailMix]
@[simp] theorem tailMix_one (a b : Tail) : tailMix a b 1 = b := by
  cases a; cases b; simp [tailMix]

end
end Rho5.ExternalBFibreCapacity
