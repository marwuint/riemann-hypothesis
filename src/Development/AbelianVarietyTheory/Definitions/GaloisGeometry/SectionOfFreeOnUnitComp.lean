import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsGrothendieckAbelianPresheaf

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian

namespace GlobalTheory.Et

section Restriction

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

variable (R) in

def sectionOf (X : Scheme.{0}) (F : Shv R) : ((freeOn R).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (ChangeRing.freeEquiv Scheme.proetaleTopology.{0} (uliftYoneda.{1}.obj X) F).trans uliftYonedaEquiv

end Restriction

end GlobalTheory.Et

end
