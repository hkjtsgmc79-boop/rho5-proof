import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Max

/-! Frozen pilot conventions. `q` always denotes the actual coordinate. -/
namespace Rho5

abbrev Matrix5 := Matrix (Fin 5) (Fin 5) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

noncomputable def matrixEntryMax (M : Matrix5) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|)

/-- The norm of a finite function is the coordinate sup norm. -/
noncomputable def vectorSup (n : ℕ) (v : Vec n) : ℝ := ‖v‖

/-- The continuous linear map norm is the induced operator norm, not entry-max. -/
noncomputable def jacobianOperatorNorm (n m : ℕ) (J : Vec n →L[ℝ] Vec m) : ℝ := ‖J‖

inductive B17Coord
  | k | A | B | c | d | u0 | u1 | u2 | x0 | x1 | x2 | v0 | v1 | v2 | q0 | q1 | q2
  deriving DecidableEq, Repr

inductive B24Coord
  | k | r | s | t | A | B | c | d | p | e | beta
  | u0 | u1 | u2 | x0 | x1 | x2 | v0 | v1 | v2 | q0 | q1 | q2 | F
  deriving DecidableEq, Repr

noncomputable def bHeight (r s t : ℝ) : ℝ := r + s * t / r
def xHeight (r w : ℝ) : ℝ := r - w

/-- Qualification is separate: total real division does not certify a physical source. -/
def bHeightQualified (r : ℝ) : Prop := r ≠ 0

end Rho5
