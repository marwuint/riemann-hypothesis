import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian

namespace GlobalTheory.Et.Small

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

structure Good {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] (Φ : A ⥤ B) : Prop where
  lim : PreservesFiniteLimits Φ
  colim : PreservesFiniteColimits Φ
  inj : Φ.PreservesInjectiveObjects

theorem Good.comp {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃} [Category.{v₃} C]
    {Φ : A ⥤ B} {Ψ : B ⥤ C} (h : Good Φ) (h' : Good Ψ) : Good (Φ ⋙ Ψ) := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨_, _, _⟩ := h'
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _, inferInstance⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem lan_preservesFiniteLimits {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : Type u₃) [Category.{v₃} E] [HasFiniteLimits E] (F : C ⥤ D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E]
    (h : ∀ X : D, HasExactColimitsOfShape (CostructuredArrow F X) E) :
    PreservesFiniteLimits (F.lan : (C ⥤ E) ⥤ D ⥤ E) := by
  have e (X : D) : F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
    NatIso.ofComponents (fun G =>
      IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
        intro T
        have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
        have h₂ := congr_app (F.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.lan : (C ⥤ E) ⥤ D ⥤ E) J
  intro K
  have := (h K).preservesFiniteLimits
  exact preservesLimitsOfShape_of_natIso (e K).symm

variable (R : Type) [CommRing R]

def restrict (X : Scheme.{0}) : Shv R ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{1} :=
  sheafCompose _ (forget₂ (ModuleCat.{1} (ULift.{1} R)) Ab.{1}) ⋙
    (Over.forget X).sheafPushforwardContinuous Ab.{1} (Scheme.proetaleTopology.over X) Scheme.proetaleTopology ⋙
    (Scheme.ProEt.forget X).sheafPushforwardContinuous Ab.{1} (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)

def freeOnEquiv (X : Scheme.{0}) (F : Shv R) : ((freeOn R).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction _ _).homEquiv _ F).trans
    (((((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ)).homEquiv (uliftYoneda.{1}.obj X) F.obj).trans
      uliftYonedaEquiv)

theorem freeOnEquiv_comp (X : Scheme.{0}) {F G : Shv R} (g : (freeOn R).obj X ⟶ F) (f : F ⟶ G) :
    freeOnEquiv R X G (g ≫ f) = f.hom.app (op X) (freeOnEquiv R X F g) := rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

end GlobalTheory.Et.Small

end
