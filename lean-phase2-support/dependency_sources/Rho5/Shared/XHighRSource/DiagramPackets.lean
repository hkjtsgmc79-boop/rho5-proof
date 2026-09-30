import Rho5.Shared.XHighRSource.SourceRows

/-!
# D145 stage B — the two high diagrams' actual `P0`–`P3` packet source rows

This module carries the **archived packet recipes** (`fixed_source/source/factor_oracle.hpp`
`make_factor_packets`) as Lean functions of a source box, for both head types, and connects them to
the actual X source point:

* `stagePacket` (`X`), `origPacket` (`Y`, head type I = `G` on `e*beta`, type II = `G` on `e*u0`)
  and `corePacket` (`C`), exactly the archived `a`/`b`/`z` dictionaries and meets
  (`one = [-1,1]`, the constant factor `1 = [1,1]`, the head band `p ∓ 1`, the `G` clamp);
* **realization bridges**: a box that contains the actual 23-coordinate source point realizes each
  packet with the source's own factors (`1, x_i` against `p, q_j`; `e, u_i` against `beta, v_j`;
  `c, d` against `k, A, B`) — pure interval-arithmetic soundness, no source assumption;
* the **`P0`–`P3` rejection transfers** for each packet: an empty packet interval, or a closed
  constraint cycle of weight product `< 1` on the box's own packet with the source's positive
  factors, refutes every source point of the box;
* the **missing-bound responsibility in Lean**: the closed outer box grants no strict high-`r`
  qualification to `r = k` sources.

The head rows (`head+`/`head-`) are consumed as the explicit hypothesis `HeadRows`; they are the
package's own rows for the actual source, never assumed globally.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Shared.V43MatrixRoundTrip

/-- The constant factor `1` as a point interval (the archived `{UNIT2,UNIT2}`). -/
def onePt : BI := ⟨1, 1⟩

/-- The archived interval `one = [-1,1]` (`{-UNIT2,UNIT2}`), used by the packet meets. -/
def oneBand : BI := ⟨-1, 1⟩

/-- A source box: the 23 model coordinates as closed intervals (the archived `EBox`). -/
abbrev Box := Fin 23 → BI

/-- The box contains the actual 23-coordinate source point of the given head type. -/
def BoxMem (box : Box) (M : M5) (ht : HeadType) : Prop := ∀ i, (box i).Mem (modelVec M ht i)

/-- The package's head rows for the actual source: `p - 1 ≤ beta * e ≤ p + 1`
(`head+`/`head-` of `model.json`, the same rows in both head types). -/
def HeadRows (M : M5) : Prop :=
  pX M - 1 ≤ betaX M * eX M ∧ betaX M * eX M ≤ pX M + 1

/-! ## 1. The three archived packets as functions of the box -/

/-- `X.a` of `make_factor_packets`. -/
def stageA (box : Box) : Fin 4 → BI
  | 0 => onePt
  | 1 => box 13
  | 2 => box 14
  | 3 => box 15

/-- `X.b` of `make_factor_packets`. -/
def stageB (box : Box) : Fin 4 → BI
  | 0 => box 7
  | 1 => box 19
  | 2 => box 20
  | 3 => box 21

/-- `X.z`: the `p`/`q` row itself, then the actual products `x_i q_j`. -/
def stageZ (box : Box) : Fin 4 → Fin 4 → BI
  | 0, j => stageB box j
  | 1, j => (stageA box 1).times (stageB box j)
  | 2, j => (stageA box 2).times (stageB box j)
  | 3, j => (stageA box 3).times (stageB box j)

/-- The archived stage packet `X`. -/
def stagePacket (box : Box) : Packet 4 4 := ⟨stageA box, stageB box, stageZ box⟩

/-- `Y.a` of `make_factor_packets`: `(beta, u0, u1, u2)`. -/
def origA (box : Box) : Fin 4 → BI
  | 0 => box 9
  | 1 => box 10
  | 2 => box 11
  | 3 => box 12

/-- `Y.b` of `make_factor_packets`: `(e, v0, v1, v2)`. -/
def origB (box : Box) : Fin 4 → BI
  | 0 => box 8
  | 1 => box 16
  | 2 => box 17
  | 3 => box 18

/-- `Y.z` for **type I** (`G = e*beta`): the head row is `(0,0)`. -/
def origZI (box : Box) : Fin 4 → Fin 4 → BI
  | 0, 0 => (((origA box 0).times (origB box 0)).meet ((box 7).minus oneBand)).meet (box 22)
  | 0, 1 => (origA box 0).times (origB box 1)
  | 0, 2 => (origA box 0).times (origB box 2)
  | 0, 3 => (origA box 0).times (origB box 3)
  | 1, 0 => (origA box 1).times (origB box 0)
  | 1, 1 => (origA box 1).times (origB box 1)
  | 1, 2 => (origA box 1).times (origB box 2)
  | 1, 3 => (origA box 1).times (origB box 3)
  | 2, 0 => (origA box 2).times (origB box 0)
  | 2, 1 => (origA box 2).times (origB box 1)
  | 2, 2 => (origA box 2).times (origB box 2)
  | 2, 3 => (origA box 2).times (origB box 3)
  | 3, 0 => (origA box 3).times (origB box 0)
  | 3, 1 => (origA box 3).times (origB box 1)
  | 3, 2 => (origA box 3).times (origB box 2)
  | 3, 3 => (origA box 3).times (origB box 3)

/-- `Y.z` for **type II** (`G = e*u0`): the head row is `(1,0)`. -/
def origZII (box : Box) : Fin 4 → Fin 4 → BI
  | 0, 0 => ((origA box 0).times (origB box 0)).meet ((box 7).minus oneBand)
  | 0, 1 => (origA box 0).times (origB box 1)
  | 0, 2 => (origA box 0).times (origB box 2)
  | 0, 3 => (origA box 0).times (origB box 3)
  | 1, 0 => ((origA box 1).times (origB box 0)).meet (box 22)
  | 1, 1 => (origA box 1).times (origB box 1)
  | 1, 2 => (origA box 1).times (origB box 2)
  | 1, 3 => (origA box 1).times (origB box 3)
  | 2, 0 => (origA box 2).times (origB box 0)
  | 2, 1 => (origA box 2).times (origB box 1)
  | 2, 2 => (origA box 2).times (origB box 2)
  | 2, 3 => (origA box 2).times (origB box 3)
  | 3, 0 => (origA box 3).times (origB box 0)
  | 3, 1 => (origA box 3).times (origB box 1)
  | 3, 2 => (origA box 3).times (origB box 2)
  | 3, 3 => (origA box 3).times (origB box 3)

/-- The head-type-selected `Y.z` (the archived `HEAD_TYPE`). -/
def origZ (ht : HeadType) (box : Box) : Fin 4 → Fin 4 → BI :=
  match ht with
  | .I => origZI box
  | .II => origZII box

/-- The archived original packet `Y`. -/
def origPacket (ht : HeadType) (box : Box) : Packet 4 4 :=
  ⟨origA box, origB box, origZ ht box⟩

/-- `C.a` of `make_factor_packets`. -/
def coreA (box : Box) : Fin 2 → BI
  | 0 => box 5
  | 1 => box 6

/-- `C.b` of `make_factor_packets`. -/
def coreB (box : Box) : Fin 3 → BI
  | 0 => box 0
  | 1 => box 3
  | 2 => box 4

/-- `C.z`: the actual products `c k`, `c A`, `c B`, `d k`, `d A`, `d B`. -/
def coreZ (box : Box) : Fin 2 → Fin 3 → BI
  | 0, 0 => (coreA box 0).times (coreB box 0)
  | 0, 1 => (coreA box 0).times (coreB box 1)
  | 0, 2 => (coreA box 0).times (coreB box 2)
  | 1, 0 => (coreA box 1).times (coreB box 0)
  | 1, 1 => (coreA box 1).times (coreB box 1)
  | 1, 2 => (coreA box 1).times (coreB box 2)

/-- The archived core packet `C`. -/
def corePacket (box : Box) : Packet 2 3 := ⟨coreA box, coreB box, coreZ box⟩

/-! ## 2. The source's own factors -/

def stageLeft (M : M5) : Fin 4 → ℝ
  | 0 => 1
  | 1 => xX M 0
  | 2 => xX M 1
  | 3 => xX M 2

def stageRight (M : M5) : Fin 4 → ℝ
  | 0 => pX M
  | 1 => qX M 0
  | 2 => qX M 1
  | 3 => qX M 2

def origLeft (M : M5) : Fin 4 → ℝ
  | 0 => betaX M
  | 1 => uX M 0
  | 2 => uX M 1
  | 3 => uX M 2

def origRight (M : M5) : Fin 4 → ℝ
  | 0 => eX M
  | 1 => vX M 0
  | 2 => vX M 1
  | 3 => vX M 2

def coreLeft (M : M5) : Fin 2 → ℝ
  | 0 => cX M
  | 1 => dX M

def coreRight (M : M5) : Fin 3 → ℝ
  | 0 => kX M
  | 1 => aX M
  | 2 => bX M

/-! ## 3. Realization bridges -/

/-- **The stage packet is realized by a source box that contains the actual source point.** -/
theorem realizes_stage (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht) :
    (stagePacket box).Realizes (stageLeft M) (stageRight M) := by
  have ha : ∀ i, (stageA box i).Mem (stageLeft M i) := by
    intro i
    fin_cases i
    · exact ⟨le_refl 1, le_refl 1⟩
    · simpa [stageA, stageLeft, modelVec] using hv 13
    · simpa [stageA, stageLeft, modelVec] using hv 14
    · simpa [stageA, stageLeft, modelVec] using hv 15
  have hb : ∀ j, (stageB box j).Mem (stageRight M j) := by
    intro j
    fin_cases j
    · simpa [stageB, stageRight, modelVec] using hv 7
    · simpa [stageB, stageRight, modelVec] using hv 19
    · simpa [stageB, stageRight, modelVec] using hv 20
    · simpa [stageB, stageRight, modelVec] using hv 21
  refine ⟨ha, hb, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [stageLeft, stageRight, one_mul]
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact hb 3
  · exact BI.mem_times (ha 1) (hb 0)
  · exact BI.mem_times (ha 1) (hb 1)
  · exact BI.mem_times (ha 1) (hb 2)
  · exact BI.mem_times (ha 1) (hb 3)
  · exact BI.mem_times (ha 2) (hb 0)
  · exact BI.mem_times (ha 2) (hb 1)
  · exact BI.mem_times (ha 2) (hb 2)
  · exact BI.mem_times (ha 2) (hb 3)
  · exact BI.mem_times (ha 3) (hb 0)
  · exact BI.mem_times (ha 3) (hb 1)
  · exact BI.mem_times (ha 3) (hb 2)
  · exact BI.mem_times (ha 3) (hb 3)

/-- The head product lies in the archived head band `[p - 1, p + 1]` when the package's head rows
hold. -/
theorem headBand_mem (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hh : HeadRows M) : ((box 7).minus oneBand).Mem (betaX M * eX M) := by
  obtain ⟨h1, h2⟩ := hh
  have hp1 : (box 7).lo ≤ pX M := (hv 7).1
  have hp2 : pX M ≤ (box 7).hi := (hv 7).2
  refine ⟨?_, ?_⟩ <;> simp only [BI.minus, oneBand] <;> linarith

/-- **The original packet is realized by a source box that contains the actual source point**, for
either head type.  Type I clamps the `(0,0)` entry (`G = e*beta`), type II the `(1,0)` entry
(`G = e*u0`) — the archived `HEAD_TYPE`. -/
theorem realizes_orig (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hh : HeadRows M) :
    (origPacket ht box).Realizes (origLeft M) (origRight M) := by
  have ha : ∀ i, (origA box i).Mem (origLeft M i) := by
    intro i
    fin_cases i
    · simpa [origA, origLeft, modelVec] using hv 9
    · simpa [origA, origLeft, modelVec] using hv 10
    · simpa [origA, origLeft, modelVec] using hv 11
    · simpa [origA, origLeft, modelVec] using hv 12
  have hb : ∀ j, (origB box j).Mem (origRight M j) := by
    intro j
    fin_cases j
    · simpa [origB, origRight, modelVec] using hv 8
    · simpa [origB, origRight, modelVec] using hv 16
    · simpa [origB, origRight, modelVec] using hv 17
    · simpa [origB, origRight, modelVec] using hv 18
  cases ht with
  | I =>
      have hG : (box 22).Mem (betaX M * eX M) := by
        have h22 := hv 22
        simpa [modelVec, Gmodel, mul_comm] using h22
      refine ⟨ha, hb, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j
      · exact BI.mem_meet (BI.mem_meet (BI.mem_times (ha 0) (hb 0))
          (headBand_mem box M .I hv hh)) hG
      · exact BI.mem_times (ha 0) (hb 1)
      · exact BI.mem_times (ha 0) (hb 2)
      · exact BI.mem_times (ha 0) (hb 3)
      · exact BI.mem_times (ha 1) (hb 0)
      · exact BI.mem_times (ha 1) (hb 1)
      · exact BI.mem_times (ha 1) (hb 2)
      · exact BI.mem_times (ha 1) (hb 3)
      · exact BI.mem_times (ha 2) (hb 0)
      · exact BI.mem_times (ha 2) (hb 1)
      · exact BI.mem_times (ha 2) (hb 2)
      · exact BI.mem_times (ha 2) (hb 3)
      · exact BI.mem_times (ha 3) (hb 0)
      · exact BI.mem_times (ha 3) (hb 1)
      · exact BI.mem_times (ha 3) (hb 2)
      · exact BI.mem_times (ha 3) (hb 3)
  | II =>
      have hGu : (box 22).Mem (uX M 0 * eX M) := by
        have h22 := hv 22
        simpa [modelVec, Gmodel, mul_comm] using h22
      refine ⟨ha, hb, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j
      · exact BI.mem_meet (BI.mem_times (ha 0) (hb 0)) (headBand_mem box M .II hv hh)
      · exact BI.mem_times (ha 0) (hb 1)
      · exact BI.mem_times (ha 0) (hb 2)
      · exact BI.mem_times (ha 0) (hb 3)
      · exact BI.mem_meet (BI.mem_times (ha 1) (hb 0)) hGu
      · exact BI.mem_times (ha 1) (hb 1)
      · exact BI.mem_times (ha 1) (hb 2)
      · exact BI.mem_times (ha 1) (hb 3)
      · exact BI.mem_times (ha 2) (hb 0)
      · exact BI.mem_times (ha 2) (hb 1)
      · exact BI.mem_times (ha 2) (hb 2)
      · exact BI.mem_times (ha 2) (hb 3)
      · exact BI.mem_times (ha 3) (hb 0)
      · exact BI.mem_times (ha 3) (hb 1)
      · exact BI.mem_times (ha 3) (hb 2)
      · exact BI.mem_times (ha 3) (hb 3)

/-- **The core packet is realized by a source box that contains the actual source point.** -/
theorem realizes_core (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht) :
    (corePacket box).Realizes (coreLeft M) (coreRight M) := by
  have ha : ∀ i, (coreA box i).Mem (coreLeft M i) := by
    intro i
    fin_cases i
    · simpa [coreA, coreLeft, modelVec] using hv 5
    · simpa [coreA, coreLeft, modelVec] using hv 6
  have hb : ∀ j, (coreB box j).Mem (coreRight M j) := by
    intro j
    fin_cases j
    · simpa [coreB, coreRight, modelVec] using hv 0
    · simpa [coreB, coreRight, modelVec] using hv 3
    · simpa [coreB, coreRight, modelVec] using hv 4
  refine ⟨ha, hb, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact BI.mem_times (ha 0) (hb 0)
  · exact BI.mem_times (ha 0) (hb 1)
  · exact BI.mem_times (ha 0) (hb 2)
  · exact BI.mem_times (ha 1) (hb 0)
  · exact BI.mem_times (ha 1) (hb 1)
  · exact BI.mem_times (ha 1) (hb 2)

/-! ## 4. `P0`–`P3` rejection transfers to the source box -/

/-- `P3` on the stage packet: an empty packet interval refutes every source point of the box. -/
theorem no_source_of_stage_empty (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    {i : Fin 4} (h : (stageA box i).Empty) : False :=
  (Packet.not_realizes_of_empty_a (P := stagePacket box) h) (realizes_stage box M ht hv)

/-- `P0`/`P3` on the original packet, at a factor interval. -/
theorem no_source_of_orig_empty (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hh : HeadRows M) {i : Fin 4} (h : (origA box i).Empty) : False :=
  (Packet.not_realizes_of_empty_a (P := origPacket ht box) h) (realizes_orig box M ht hv hh)

/-- `P0`/`P3` on the core packet, at a factor interval. -/
theorem no_source_of_core_empty (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    {i : Fin 2} (h : (coreA box i).Empty) : False :=
  (Packet.not_realizes_of_empty_a (P := corePacket box) h) (realizes_core box M ht hv)

/-- **`P2` on the stage packet, at the source's own positive factors**: a closed constraint chain
of the box's packet whose weight product is `< 1` refutes every source point of the box. -/
theorem no_source_of_stage_cycle (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hposA : ∀ i, 0 < stageLeft M i) (hposB : ∀ j, 0 < stageRight M j)
    {u : PVert 4 4} {l : List (PVert 4 4 × ℝ)}
    (hwpos : ∀ u w v, PEdge (stagePacket box) u w v → 0 < w)
    (hwalk : Walk (PEdge (stagePacket box)) u l u)
    (hsmall : (l.map Prod.snd).prod < 1) : False :=
  (not_realizes_of_cycle hwpos hwalk hsmall)
    ⟨stageLeft M, stageRight M, realizes_stage box M ht hv, hposA, hposB⟩

/-- **`P2` on the original packet**, at the source's own positive factors. -/
theorem no_source_of_orig_cycle (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hh : HeadRows M) (hposA : ∀ i, 0 < origLeft M i) (hposB : ∀ j, 0 < origRight M j)
    {u : PVert 4 4} {l : List (PVert 4 4 × ℝ)}
    (hwpos : ∀ u w v, PEdge (origPacket ht box) u w v → 0 < w)
    (hwalk : Walk (PEdge (origPacket ht box)) u l u)
    (hsmall : (l.map Prod.snd).prod < 1) : False :=
  (not_realizes_of_cycle hwpos hwalk hsmall)
    ⟨origLeft M, origRight M, realizes_orig box M ht hv hh, hposA, hposB⟩

/-- **`P2` on the core packet**, at the source's own positive factors. -/
theorem no_source_of_core_cycle (box : Box) (M : M5) (ht : HeadType) (hv : BoxMem box M ht)
    (hposA : ∀ i, 0 < coreLeft M i) (hposB : ∀ j, 0 < coreRight M j)
    {u : PVert 2 3} {l : List (PVert 2 3 × ℝ)}
    (hwpos : ∀ u w v, PEdge (corePacket box) u w v → 0 < w)
    (hwalk : Walk (PEdge (corePacket box)) u l u)
    (hsmall : (l.map Prod.snd).prod < 1) : False :=
  (not_realizes_of_cycle hwpos hwalk hsmall)
    ⟨coreLeft M, coreRight M, realizes_core box M ht hv, hposA, hposB⟩

/-! ## 5. Missing-bound responsibility, in Lean -/

/-- **The closed outer box grants no strict high-`r` qualification**: a source with `k = r`
satisfies the models' closed outer box yet lies outside the strict high-`r` domain, so the two
diagrams' closed outer box cannot be read as covering arbitrary `r = k` sources. -/
theorem closedOuter_no_high_qualification (M : M5) (h : ClosedOuterBox M) (hkr : rX M = kX M) :
    ¬ HighRDomain (extractX M) := by
  refine not_highR_of_r_eq_k (extractX M) ?_
  simp only [extractX_0, extractX_1]
  exact hkr

end

end Rho5.Shared.XHighRSource
