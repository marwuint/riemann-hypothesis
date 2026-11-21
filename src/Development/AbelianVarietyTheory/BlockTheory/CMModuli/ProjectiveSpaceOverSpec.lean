import Mathlib

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

attribute [local instance] MvPolynomial.gradedAlgebra

def IsIndEtale {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale) (CommRingCat.ofHom φ)

def IsStrictHenselisation {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (φ : A →+* S) : Prop :=
  HenselianLocalRing S ∧ IsSepClosed (ResidueField S) ∧ IsLocalHom φ ∧ IsIndEtale φ

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec
