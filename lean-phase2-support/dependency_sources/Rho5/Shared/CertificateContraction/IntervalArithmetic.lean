import Rho5.Shared.CertificateContraction.Composition
import Rho5.Certificate.B16.LiftBox.IntervalMul

namespace Rho5.Shared.CertificateContraction

structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def QInterval.Contains (b : QInterval) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def QInterval.point (q : ℚ) : QInterval := ⟨q, q⟩
def QInterval.add (a b : QInterval) : QInterval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def QInterval.neg (a : QInterval) : QInterval := ⟨-a.hi, -a.lo⟩
def QInterval.mul (a b : QInterval) : QInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

theorem QInterval.point_contains (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩
theorem QInterval.add_contains (a b : QInterval) (x y : ℝ)
    (ha : a.Contains x) (hb : b.Contains y) : (a.add b).Contains (x+y) := by
  constructor <;> dsimp [add] <;> push_cast
  · exact add_le_add ha.1 hb.1
  · exact add_le_add ha.2 hb.2

theorem QInterval.neg_contains (a : QInterval) (x : ℝ) (ha : a.Contains x) :
    a.neg.Contains (-x) := by
  constructor <;> dsimp [neg] <;> push_cast
  · exact neg_le_neg ha.2
  · exact neg_le_neg ha.1

theorem QInterval.mul_contains (a b : QInterval) (x y : ℝ)
    (ha : a.Contains x) (hb : b.Contains y) : (a.mul b).Contains (x*y) := by
  constructor <;> dsimp [mul] <;> push_cast
  · apply Rho5.Certificate.B16.LiftBox.mul_lo_of_corners ha hb <;> simp [min_le_iff]
  · apply Rho5.Certificate.B16.LiftBox.mul_hi_of_corners ha hb <;> simp [le_max_iff]

def Box.interval {n : ℕ} (b : Box n) (i : Fin n) : QInterval := ⟨b.lo i,b.hi i⟩

theorem Box.interval_contains {n : ℕ} (b : Box n) (z : Fin n → ℝ)
    (hb : b.Contains z) (i : Fin n) : (b.interval i).Contains (z i) := hb i

end Rho5.Shared.CertificateContraction
