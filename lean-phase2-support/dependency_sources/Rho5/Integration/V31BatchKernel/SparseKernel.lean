import Rho5.Integration.V31BatchKernel.IntegerSyntax

namespace Rho5.Integration.V31BatchKernel

/-- Every repeated column contributes by addition. Zero sums may remain. -/
def insertAdd {N : ℕ} (i : Fin N) (c : ℤ) : ITerms N → ITerms N
  | [] => [(i,c)]
  | (j,d)::ts => if i = j then (j,d+c)::ts else (j,d)::insertAdd i c ts

theorem eval_insertAdd {N : ℕ} (i : Fin N) (c : ℤ) (ts : ITerms N) (y : Fin N → ℝ) :
    iEval y (insertAdd i c ts) = (c : ℝ) * y i + iEval y ts := by
  induction ts with
  | nil => simp [insertAdd, iEval]
  | cons t ts ih =>
    rcases t with ⟨j,d⟩
    by_cases h : i = j
    · subst j; simp [insertAdd, iEval, Int.cast_add, add_mul] <;> ring
    · simp [insertAdd, iEval, h, ih] <;> ring

def addScaled {N : ℕ} (w : ℤ) : ITerms N → ITerms N → ITerms N
  | [], acc => acc
  | (i,c)::ts, acc => addScaled w ts (insertAdd i (w*c) acc)

theorem eval_addScaled {N : ℕ} (w : ℤ) (ts acc : ITerms N) (y : Fin N → ℝ) :
    iEval y (addScaled w ts acc) = (w : ℝ) * iEval y ts + iEval y acc := by
  induction ts generalizing acc with
  | nil => simp [addScaled, iEval]
  | cons t ts ih =>
    rcases t with ⟨i,c⟩
    rw [addScaled, ih, eval_insertAdd]
    simp only [iEval, Int.cast_mul]
    ring

def weightedAdd {N : ℕ} (w : ℤ) (r acc : IRow N) : IRow N :=
  ⟨addScaled w r.terms acc.terms, w*r.rhs+acc.rhs⟩

theorem weightedAdd_holds {N : ℕ} {w : ℤ} {r acc : IRow N} {y : Fin N → ℝ}
    (hw : 0 ≤ w) (hr : r.Holds y) (ha : acc.Holds y) :
    (weightedAdd w r acc).Holds y := by
  change iEval y (addScaled w r.terms acc.terms) ≤ ((w*r.rhs+acc.rhs : ℤ) : ℝ)
  rw [eval_addScaled]
  simp only [Int.cast_add, Int.cast_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hr (by exact_mod_cast hw)) ha

abbrev Support := List (ℕ × ℤ)
def accumulate {N : ℕ} (rows : ℕ → IRow N) : Support → IRow N → IRow N
  | [], acc => acc
  | (rid,w)::rest, acc => accumulate rows rest (weightedAdd w (rows rid) acc)
def combine {N : ℕ} (rows : ℕ → IRow N) (s : Support) : IRow N :=
  accumulate rows s ⟨[],0⟩

theorem accumulate_holds {N : ℕ} (rows : ℕ → IRow N) (s : Support) (y : Fin N → ℝ) :
    (∀ p ∈ s, 0 ≤ p.2 ∧ (rows p.1).Holds y) →
    ∀ acc, acc.Holds y → (accumulate rows s acc).Holds y := by
  induction s with
  | nil => intro hs acc ha; simpa only [accumulate] using ha
  | cons p s ih =>
    intro hs acc ha
    have hp := hs p (by simp)
    exact ih (fun q hq => hs q (List.mem_cons_of_mem p hq)) (weightedAdd p.2 (rows p.1) acc)
      (weightedAdd_holds hp.1 hp.2 ha)

theorem combine_holds {N : ℕ} (rows : ℕ → IRow N) (s : Support) (y : Fin N → ℝ)
    (hs : ∀ p ∈ s, 0 ≤ p.2 ∧ (rows p.1).Holds y) : (combine rows s).Holds y :=
  accumulate_holds rows s y hs ⟨[],0⟩ (by simp [IRow.Holds, iEval])

def boxMin {N : ℕ} (b : IBox N) : ITerms N → ℤ
  | [] => 0
  | (i,c)::ts => min (c*b.lo i) (c*b.hi i) + boxMin b ts

theorem term_lower (c l u : ℤ) (z : ℝ) (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) :
    ((min (c*l) (c*u) : ℤ) : ℝ) ≤ (c : ℝ)*z := by
  by_cases hc : 0 ≤ c
  · calc
      _ ≤ ((c*l : ℤ) : ℝ) := by exact_mod_cast (min_le_left (c*l) (c*u))
      _ ≤ (c : ℝ)*z := by
        rw [Int.cast_mul]
        exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hc)
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    calc
      _ ≤ ((c*u : ℤ) : ℝ) := by exact_mod_cast (min_le_right (c*l) (c*u))
      _ ≤ (c : ℝ)*z := by
        rw [Int.cast_mul]
        exact mul_le_mul_of_nonpos_left hu hc'

theorem boxMin_sound {N : ℕ} (b : IBox N) (ts : ITerms N) (y : Fin N → ℝ)
    (hb : b.Contains y) : (boxMin b ts : ℝ) ≤ iEval y ts := by
  induction ts with
  | nil => simp [boxMin, iEval]
  | cons t ts ih =>
    rcases t with ⟨i,c⟩
    simp only [boxMin, iEval, Int.cast_add]
    exact add_le_add (term_lower c (b.lo i) (b.hi i) (y i) (hb i).1 (hb i).2) ih

theorem margin_false {N : ℕ} (C : IRow N) (b : IBox N) (y : Fin N → ℝ)
    (hC : C.Holds y) (hb : b.Contains y) (hm : C.rhs < boxMin b C.terms) : False := by
  have hlo := boxMin_sound b C.terms y hb
  have hlt : (C.rhs : ℝ) < (boxMin b C.terms : ℝ) := by exact_mod_cast hm
  exact (not_lt_of_ge (le_trans hlo hC)) hlt

inductive Verdict where
  | invalid
  | pending
  | closed
  deriving DecidableEq, Repr

def supportOK (rowCount : ℕ) (s : Support) : Bool :=
  s.all (fun p => decide (p.1 < rowCount ∧ 0 < p.2)) && decide (s.map Prod.fst).Nodup

/-- Validate first. Invalid IDs or nonpositive weights never reach combination. -/
def terminalCheck {N : ℕ} (rowCount : ℕ) (rows : ℕ → IRow N) (b : IBox N) (s : Support) : Verdict :=
  if b.ordered && supportOK rowCount s then
    let C := combine rows s
    if C.rhs < boxMin b C.terms then .closed else .pending
  else .invalid

theorem supportOK_sound (rowCount : ℕ) (s : Support) (h : supportOK rowCount s = true)
    (p : ℕ × ℤ) (hp : p ∈ s) : p.1 < rowCount ∧ 0 < p.2 := by
  have hh : (∀ p ∈ s, p.1 < rowCount ∧ 0 < p.2) ∧ (s.map Prod.fst).Nodup := by
    simpa [supportOK] using h
  exact hh.1 p hp

theorem terminalCheck_sound {N : ℕ} (rowCount : ℕ) (rows : ℕ → IRow N) (b : IBox N)
    (s : Support) (hc : terminalCheck rowCount rows b s = .closed)
    (y : Fin N → ℝ) (hb : b.Contains y) (hr : ∀ i, i < rowCount → (rows i).Holds y) : False := by
  unfold terminalCheck at hc
  split at hc
  · rename_i hok
    dsimp only at hc
    split at hc
    · rename_i hmargin
      apply margin_false (combine rows s) b y ?_ hb hmargin
      apply combine_holds
      intro p hp
      have hs : supportOK rowCount s = true := by
        have h : b.ordered = true ∧ supportOK rowCount s = true := by simpa only [Bool.and_eq_true] using hok
        exact h.2
      have h := supportOK_sound rowCount s hs p hp
      exact ⟨le_of_lt h.2, hr p.1 h.1⟩
    · cases hc
  · cases hc

end Rho5.Integration.V31BatchKernel
