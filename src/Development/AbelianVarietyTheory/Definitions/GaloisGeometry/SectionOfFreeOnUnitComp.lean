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

abbrev resShv : Shv S ⥤ Shv R := ChangeRing.res Scheme.proetaleTopology.{0} (RingHom.ulift.{1, 1} φ)

def freeOnUnit (X : Scheme.{0}) : (freeOn R).obj X ⟶ (resShv φ).obj ((freeOn S).obj X) :=
  ChangeRing.freeUnit _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X)

def resEquivHS (G : Shv S) (n : ℕ) (X : Scheme.{0}) : HS S G n X ≃+ HS R ((resShv φ).obj G) n X :=
  ChangeRing.cmp _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X) G n

theorem resEquivHS_apply (G : Shv S) (n : ℕ) (X : Scheme.{0}) (y : HS S G n X) :
    resEquivHS φ G n X y = (Ext.mk₀ (freeOnUnit φ X)).comp (y.mapExactFunctor (resShv φ)) (zero_add n) := rfl

variable (R) in

def sectionOf (X : Scheme.{0}) (F : Shv R) : ((freeOn R).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (ChangeRing.freeEquiv Scheme.proetaleTopology.{0} (uliftYoneda.{1}.obj X) F).trans uliftYonedaEquiv

theorem sectionOf_comp (X : Scheme.{0}) {F G : Shv R} (g : (freeOn R).obj X ⟶ F) (u : F ⟶ G) :
    sectionOf R X G (g ≫ u) = u.hom.app (op X) (sectionOf R X F g) := rfl

end Restriction

end GlobalTheory.Et

end
