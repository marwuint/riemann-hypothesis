import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC

open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := GlobalTheory.AICIff.aic_iff
