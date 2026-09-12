import Rho5.Algebraic.CriticalExistence.Circuit
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# D50 phase A — the 16 weighted contraction-slope arithmetic bounds

The frozen G04 `Circuit` layer (`Rho5.Algebraic.CriticalExistence.Circuit`) fixes the
four `errorIntervals` rows and the four radius coordinates `radQ`/`radius`.  This
module proves, directly and in a separate file, the sixteen weighted bounds that the
contraction-slope estimate needs:

for **every** `i j : Fin 4`,

`(max |(errorIntervals i j).lo| |(errorIntervals i j).hi| : ℚ) * radius j ≤ radius i / 16`.

The quantity is exactly the card's: the magnitude `max |lo| |hi|` of the frozen
rational interval (a `ℚ` coerced to `ℝ`), multiplied by the frozen radius `radius j`
and bounded by `radius i / 16`.  Nothing is regenerated, no constant or interval is
changed, and no sampling is used: each of the sixteen cases is closed by rational
arithmetic on the frozen literals.

`magnitude` is only a naming abbreviation for that same `max` (allowed by the card so
the statements stay readable); `slope_arith` states the public goal with the literal
expression and `slope_arith_magnitude` restates it through the name.

Scope: phase A of the card only.  The secant/jet connection (`concrete_slopes`) is
phase B and is gated on D39's published `JET_READY.json`; nothing here asserts a jet
or slope conclusion, and no jet module is imported.
-/

namespace Rho5.Algebraic.CriticalExistence.SlopeBoundReady

open Rho5.Algebraic.CriticalExistence

/-- The magnitude of a frozen `errorIntervals` entry: `max |lo| |hi|`, in `ℚ`.
This is a *name* for the card's quantity, not a new bound. -/
def magnitude (i j : Fin 4) : ℚ := max |(errorIntervals i j).lo| |(errorIntervals i j).hi|

/-- **Phase A (rational form).**  All sixteen weighted bounds, stated in `ℚ`. -/
theorem slope_arith_rat (i j : Fin 4) : magnitude i j * radQ j ≤ radQ i / 16 := by
  fin_cases i <;> fin_cases j <;>
    simp only [magnitude, errorIntervals, radQ, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.isValue] <;>
    norm_num

/-- **Phase A (public form, exactly the card's quantity).**  For every `i j : Fin 4`
the frozen interval magnitude times the frozen radius is bounded by `radius i / 16`. -/
theorem slope_arith (i j : Fin 4) :
    (((max |(errorIntervals i j).lo| |(errorIntervals i j).hi| : ℚ) : ℝ) * radius j
      ≤ radius i / 16) := by
  have h := slope_arith_rat i j
  have h' : ((magnitude i j : ℚ) : ℝ) * ((radQ j : ℚ) : ℝ) ≤ ((radQ i : ℚ) : ℝ) / 16 := by
    exact_mod_cast h
  simpa [magnitude, radius] using h'

/-- The same bound written through the `magnitude` name. -/
theorem slope_arith_magnitude (i j : Fin 4) :
    ((magnitude i j : ℚ) : ℝ) * radius j ≤ radius i / 16 := by
  simpa [magnitude] using slope_arith i j

/-- The sixteen bounds as a single universally quantified statement (the shape a
downstream `concrete_slopes` proof consumes row by row). -/
theorem slope_arith_all :
    ∀ i j : Fin 4,
      (((max |(errorIntervals i j).lo| |(errorIntervals i j).hi| : ℚ) : ℝ) * radius j
        ≤ radius i / 16) :=
  fun i j => slope_arith i j

theorem magnitude_nonneg (i j : Fin 4) : 0 ≤ magnitude i j :=
  le_max_of_le_left (abs_nonneg _)

end Rho5.Algebraic.CriticalExistence.SlopeBoundReady
