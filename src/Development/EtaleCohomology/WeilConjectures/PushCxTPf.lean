import Development.EtaleCohomology.WeilConjectures.ArtinCut
import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.EWeil.ArtinCut

namespace LateralTheory.EWeil.PushCxTPf

def tot {A B : CommRingCat.{0}} (β : A ⟶ B) : (Spec A).Etale ⥤ Scheme.{0} :=
  MorphismProperty.Over.forget _ _ _ ⋙ Over.pullback (Spec.map β) ⋙ Over.forget _

def pushP {R : Type} [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R) :
    ((Spec A).Etale)ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  (tot β).op ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} R)) AddCommGrpCat.{1}

def SheafP : Prop := ∀ (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R),
  Presheaf.IsSheaf (Spec A).smallEtaleTopology (pushP β F)

def pushF (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : Shv R ⥤ Sm A where
  obj F := ⟨pushP β F, hS R β F⟩
  map φ := ⟨Functor.whiskerRight (Functor.whiskerLeft (tot β).op φ.hom) (forget₂ _ _)⟩

instance (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : (pushF hS R β).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

end LateralTheory.EWeil.PushCxTPf
