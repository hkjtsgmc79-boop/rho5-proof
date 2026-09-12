/-
D22 — axiom audit.

Each `#print axioms` below must report a subset of
`{propext, Classical.choice, Quot.sound}`.  The module introduces no `sorry`, no
project axiom and no `native_decide`; the sign hypothesis is the explicit
`IsSign r ∧ IsSign c` (equivalently `∀ i, |r i| = 1`).
-/
import Rho5.Shared.TraceSigns.Normalize

#print axioms Rho5.TraceSigns.abs_signedEntries
#print axioms Rho5.TraceSigns.isCompletePivot_signedEntries_iff
#print axioms Rho5.TraceSigns.pivotSchur_signedEntries
#print axioms Rho5.TraceSigns.legalTrace_signed_iff
#print axioms Rho5.TraceSigns.matrixEntryMax_signedEntries5
#print axioms Rho5.TraceSigns.normalize_signedEntries5
#print axioms Rho5.TraceSigns.legalTrace_normalize_signed_iff
