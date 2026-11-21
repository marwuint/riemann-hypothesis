import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
