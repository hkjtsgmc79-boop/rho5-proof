import Rho5.Shared.ActualBRootEntry.Basic

/-!
# D141 — the actual proper-B high source enters the complete B17 root

This is the assembly the card asks for.  From

* `LeadingInput M` — the actual five-step leading input on the real `5 × 5` matrix,
* `ProperB M` — the proper-B branch (`0 < r`, `0 < s < r`, `0 < t < r`, `w = -r`, balanced height),
* `alpha < height M` — the high-value hypothesis on the *actual* matrix height,

it produces a point `z'` with `NormalizedB z'`, the complete 17-dimensional `B17Root (frameOf z')`,
the same height `z' 23 = height M`, the preserved readings `k, r, s, t, p`, a strictly positive
head, and — the point of the lane — the **real row/column sign relation to `M` itself**:

`reconstruct z' i j = sg i * M i j * sg j`   with every `sg i = ±1`.

Every intermediate premise is paid here, in this order:

1. `reconstruct (extract M) = M` (the frozen extraction bridge, with `LeadingInput`/`ProperB` data);
2. `Qualified (extract M)` (D130);
3. `1 < p M` from D138's `height M ≤ 4 * p M` and `alpha > 4`;
4. `0 < e · β` from D130's head-band reading;
5. D137's head normalization of `extract M`;
6. D134's complete-root entry at the normalized head, with `alpha < z 23` transported through
   `z 23 = F M = height M`;
7. the two sign vectors composed entry by entry against `M`.

No `ResidualGap`, no `F ≤ 4p`, no `p > 1`, no `e β > 0` and no `NormalizedB` appears as a
hypothesis.  The general maximizer classification stays with D131; no whole-root safety or
capacity statement is made here.
-/

namespace Rho5.Shared.ActualBRootEntry

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Extraction (extract F p k r s t)
open Rho5.ExternalTailSaturation (LeadingInput ProperB height)
open Rho5.ExternalBFibreCapacity (NormalizedB frameOf)
open Rho5.Shared.PaperB17RootEntry (B17Root)

noncomputable section

set_option maxHeartbeats 800000

/-- **D141 — the actual proper-B high source reaches the complete B17 root.**  Every scalar
premise is paid inside; the returned sign vector is the composition of D137's head sign and
D134's/D133's corner sign, and the per-entry relation is with the original `M`. -/
theorem actual_properB_high_has_root_representative (M : Matrix5) (h : LeadingInput M)
    (hb : ProperB M) (hhigh : Rho5.Algebraic.AlphaRoot.alpha < height M) :
    ∃ (z' : Point) (sg : Fin 5 → ℝ),
      (∀ i : Fin 5, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j : Fin 5, Rho5.Certificate.B24Reconstruction.reconstruct z' i j
        = sg i * M i j * sg j) ∧
      NormalizedB z' ∧ B17Root (frameOf z') ∧
      z' 23 = height M ∧ z' 8 = p M ∧ z' 0 = k M ∧ z' 1 = r M ∧ z' 2 = s M ∧ z' 3 = t M ∧
      0 < z' 9 ∧ 0 < z' 10 ∧ Rho5.Algebraic.AlphaRoot.alpha < z' 23 := by
  -- 1. the extraction bridge: the reconstruction of the extracted point *is* the matrix
  have hre : Rho5.Certificate.B24Reconstruction.reconstruct (extract M) = M :=
    reconstruct_extract_eq M h hb
  -- 2. D130: the actual qualification layer
  have hq : Rho5.Certificate.B24MinorBridge.Qualified (extract M) :=
    Rho5.Shared.BNormalizationInterface.qualified_extract_of_properB h hb
  -- 3./4. D138 + the isolation bound, then D130: the two premises D137 needs
  have hp1 : 1 < p M := one_lt_p_of_properB_high M h hb hhigh
  have heb : 0 < Rho5.Certificate.B24Reconstruction.e (extract M)
      * Rho5.Certificate.B24Reconstruction.beta (extract M) :=
    e_mul_beta_pos_of_properB_high M h hb hhigh
  have hp1' : 1 < extract M 8 := by
    rw [Rho5.Certificate.B24Extraction.extract_eight]
    exact hp1
  have heb' : 0 < extract M 9 * extract M 10 := by
    simpa only [Rho5.Certificate.B24Reconstruction.e, Rho5.Certificate.B24Reconstruction.beta]
      using heb
  -- 5. D137: the real head normalization (one genuine row/column sign operation)
  obtain ⟨z₁, sg₁, hsg₁, hmat₁, hnorm₁, h23₁, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁, h8₁,
    h9₁, h10₁, he₁, hb₁⟩ :=
    Rho5.Shared.BHeadSign.qualified_high_head_has_normalized_representative (extract M) hq hp1' heb'
  -- the high value transported to the extracted height
  have hFh : F M = height M := F_eq_height_of_properB M hb
  have h23F : extract M 23 = F M := Rho5.Certificate.B24Extraction.extract_twentythree M
  have hhigh₁ : Rho5.Algebraic.AlphaRoot.alpha < z₁ 23 := by
    rw [h23₁, h23F, hFh]
    exact hhigh
  -- 6. D134: the complete 17-dimensional closed root
  obtain ⟨z₂, sg₂, hsg₂, hmat₂, hnorm₂, hroot₂, h23₂, h8₂, h0₂, h1₂, h2₂, h3₂, h9₂, h10₂⟩ :=
    Rho5.Shared.PaperB17RootEntry.high_normalizedB_has_canonical_root_representative z₁ hnorm₁ hhigh₁
  -- 7. assemble, composing the two real sign operations against the original `M`
  refine ⟨z₂, sgMul sg₁ sg₂, ?_, ?_, hnorm₂, hroot₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact sgMul_eq_one_or_neg_one hsg₁ hsg₂ i
  · exact reconstruct_conj_comp hre hmat₁ hmat₂
  · rw [h23₂, h23₁, h23F, hFh]
  · rw [h8₂, h8₁, Rho5.Certificate.B24Extraction.extract_eight]
  · rw [h0₂, h0₁, Rho5.Certificate.B24Extraction.extract_zero]
  · rw [h1₂, h1₁, Rho5.Certificate.B24Extraction.extract_one]
  · rw [h2₂, h2₁, Rho5.Certificate.B24Extraction.extract_two]
  · rw [h3₂, h3₁, Rho5.Certificate.B24Extraction.extract_three]
  · rw [h9₂]
    exact he₁
  · rw [h10₂]
    exact hb₁
  · rw [h23₂, h23₁, h23F, hFh]
    exact hhigh

/-- The root alone, for consumers that only need existence of a rooted same-height
representative of the actual matrix. -/
theorem exists_root_representative_of_properB_high (M : Matrix5) (h : LeadingInput M)
    (hb : ProperB M) (hhigh : Rho5.Algebraic.AlphaRoot.alpha < height M) :
    ∃ z' : Point, NormalizedB z' ∧ B17Root (frameOf z') ∧ z' 23 = height M ∧
      Rho5.Algebraic.AlphaRoot.alpha < z' 23 := by
  obtain ⟨z', sg, -, -, hnorm, hroot, h23, -, -, -, -, -, -, -, hhigh'⟩ :=
    actual_properB_high_has_root_representative M h hb hhigh
  exact ⟨z', hnorm, hroot, h23, hhigh'⟩

end

end Rho5.Shared.ActualBRootEntry
