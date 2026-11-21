import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable {R : Type} [CommRing R]

def locModule (N : Submonoid (ULift.{1} R)) : ModuleCat.{1} (ULift.{1} R) ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj A := ModuleCat.of (ULift.{1} R) (LocalizedModule N A)
  map f := ModuleCat.ofHom
    (IsLocalizedModule.map N (LocalizedModule.mkLinearMap N _) (LocalizedModule.mkLinearMap N _) f.hom)
  map_id A := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h a s => simp [IsLocalizedModule.map_LocalizedModules]
  map_comp f g := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h a s => simp [IsLocalizedModule.map_LocalizedModules]

def loc (N : Submonoid (ULift.{1} R)) : Shv R ⥤ Shv R :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (locModule N) ⋙ presheafToSheaf _ _

instance (N : Submonoid (ULift.{1} R)) : (locModule N).Additive where
  map_add {A B f g} := by
    apply ModuleCat.hom_ext
    simp only [locModule, ModuleCat.hom_add, ModuleCat.hom_ofHom, map_add]
    rfl

instance (N : Submonoid (ULift.{1} R)) : (loc N).Additive := by
  unfold loc; infer_instance

end GlobalTheory.Et

end
