import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors.TorsExt

section Affine

variable {X : Scheme.{0}} {S : Type} [CommRing S] (σ : Sp S ⟶ X)

abbrev spO (A : Type) [CommRing A] [Algebra S A] : Over X := Over.mk (spMap (algebraMap S A) ≫ σ)

def spH {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    spO σ A' ⟶ spO σ A :=
  Over.homMk (spMap φ.toRingHom) (by
    change spMap φ.toRingHom ≫ spMap (algebraMap S A) ≫ σ = spMap (algebraMap S A') ≫ σ
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact φ.comp_algebraMap)

theorem spH_left {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    (spH σ φ).left = spMap φ.toRingHom := rfl

end Affine

end GlobalTheory.FlatTors.TorsExt

namespace GlobalTheory.FlatTors

end GlobalTheory.FlatTors
