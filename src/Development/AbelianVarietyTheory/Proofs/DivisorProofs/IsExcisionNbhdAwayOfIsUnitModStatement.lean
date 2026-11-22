import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitMod

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod
