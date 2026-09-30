import Rho5.Integration.V31BatchKernel.IntegerModel
import Rho5.Integration.V31BatchKernel.SparseKernel

namespace Rho5.Integration.V31BatchKernel
open Rho5.Shared.CertificateContraction

def liftIBox {n k : ℕ} (pairs : ProductPairs n k) (b : IBox n) : IBox (n+k) where
  lo := Fin.addCases b.lo (fun q =>
    min (min (b.lo (pairs q).1*b.lo (pairs q).2) (b.lo (pairs q).1*b.hi (pairs q).2))
        (min (b.hi (pairs q).1*b.lo (pairs q).2) (b.hi (pairs q).1*b.hi (pairs q).2)))
  hi := Fin.addCases b.hi (fun q =>
    max (max (b.lo (pairs q).1*b.lo (pairs q).2) (b.lo (pairs q).1*b.hi (pairs q).2))
        (max (b.hi (pairs q).1*b.lo (pairs q).2) (b.hi (pairs q).1*b.hi (pairs q).2)))

theorem liftIBox_contains {n k : ℕ} (pairs : ProductPairs n k) (b : IBox n)
    (v : Fin n → ℝ) (hv : b.Contains v) : (liftIBox pairs b).Contains (liftPoint pairs v) := by
  apply Fin.addCases
  · intro i
    simpa [liftIBox, liftPoint] using hv i
  · intro q
    have hb := (b.contains_iff_toRat v).mp hv
    have h := QInterval.mul_contains (b.toRat.interval (pairs q).1) (b.toRat.interval (pairs q).2)
      (v (pairs q).1) (v (pairs q).2) (hb (pairs q).1) (hb (pairs q).2)
    simpa [liftIBox, liftPoint, QInterval.Contains, QInterval.mul, Box.interval, IBox.toRat, or_assoc] using h

def mccIRow {n k : ℕ} (pairs : ProductPairs n k) (b : IBox n) (q : Fin k) : Fin 4 → IRow (n+k)
  | 0 => ⟨[(Fin.castAdd k (pairs q).1,b.lo (pairs q).2),
      (Fin.castAdd k (pairs q).2,b.lo (pairs q).1),(Fin.natAdd n q,-1)],
      b.lo (pairs q).1*b.lo (pairs q).2⟩
  | 1 => ⟨[(Fin.castAdd k (pairs q).1,b.hi (pairs q).2),
      (Fin.castAdd k (pairs q).2,b.hi (pairs q).1),(Fin.natAdd n q,-1)],
      b.hi (pairs q).1*b.hi (pairs q).2⟩
  | 2 => ⟨[(Fin.castAdd k (pairs q).1,-b.hi (pairs q).2),
      (Fin.castAdd k (pairs q).2,-b.lo (pairs q).1),(Fin.natAdd n q,1)],
      -b.lo (pairs q).1*b.hi (pairs q).2⟩
  | 3 => ⟨[(Fin.castAdd k (pairs q).1,-b.lo (pairs q).2),
      (Fin.castAdd k (pairs q).2,-b.hi (pairs q).1),(Fin.natAdd n q,1)],
      -b.hi (pairs q).1*b.lo (pairs q).2⟩

theorem mccIRow_toRat {n k : ℕ} (pairs : ProductPairs n k) (b : IBox n) (q : Fin k) (f : Fin 4) :
    (mccIRow pairs b q f).toRat = mccRow pairs b.toRat q f := by
  fin_cases f <;> simp [mccIRow, IRow.toRat, mccRow, IBox.toRat]

theorem mccIRow_sound {n k : ℕ} (pairs : ProductPairs n k) (b : IBox n)
    (v : Fin n → ℝ) (hv : b.Contains v) (q : Fin k) (f : Fin 4) :
    (mccIRow pairs b q f).Holds (liftPoint pairs v) := by
  rw [IRow.holds_iff_toRat, mccIRow_toRat]
  exact mccRow_sound pairs b.toRat v ((b.contains_iff_toRat v).mp hv) q f

def typedRow {n k r : ℕ} (m : IntModel n k r) (b : IBox n) : Fin (r+k*4) → IRow (n+k) :=
  Fin.addCases (fun j => (m.ps j).toRow) (fun j => mccIRow m.pairs b j.divNat j.modNat)
def generatedIntRow {n k r : ℕ} (m : IntModel n k r) (b : IBox n) (j : ℕ) : IRow (n+k) :=
  if h : j < r+k*4 then typedRow m b ⟨j,h⟩ else ⟨[],0⟩

theorem typedRow_sound {n k r : ℕ} (m : IntModel n k r) (b : IBox n)
    (v : Fin n → ℝ) (hv : b.Contains v) (hs : m.Source v) :
    ∀ j, (typedRow m b j).Holds (liftPoint m.pairs v) := by
  apply Fin.addCases
  · intro j
    simpa [typedRow] using IPoly.row_sound m.pairs (m.ps j) v (hs j)
  · intro j
    simpa [typedRow] using mccIRow_sound m.pairs b v hv j.divNat j.modNat

theorem generatedIntRow_sound {n k r : ℕ} (m : IntModel n k r) (b : IBox n)
    (v : Fin n → ℝ) (hv : b.Contains v) (hs : m.Source v) (j : ℕ) (hj : j < r+k*4) :
    (generatedIntRow m b j).Holds (liftPoint m.pairs v) := by
  simpa [generatedIntRow, hj] using typedRow_sound m b v hv hs ⟨j,hj⟩

def leafCheck {n k r : ℕ} (m : IntModel n k r) (b : IBox n) (s : Support) : Verdict :=
  terminalCheck (r+k*4) (generatedIntRow m b) (liftIBox m.pairs b) s

theorem leafCheck_sound {n k r : ℕ} (m : IntModel n k r) (b : IBox n) (s : Support)
    (hc : leafCheck m b s = .closed) (v : Fin n → ℝ) (hv : b.Contains v) (hs : m.Source v) : False :=
  terminalCheck_sound (r+k*4) (generatedIntRow m b) (liftIBox m.pairs b) s hc
    (liftPoint m.pairs v) (liftIBox_contains m.pairs b v hv) (generatedIntRow_sound m b v hv hs)

end Rho5.Integration.V31BatchKernel
