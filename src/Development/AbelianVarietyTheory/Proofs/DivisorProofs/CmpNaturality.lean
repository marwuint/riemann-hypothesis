import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.LineQuot

variable {S T Y B : Scheme.{0}}

def cmp (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) :
    Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g' ≅ Scheme.Modules.pullback g :=
  Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w

theorem cmp_hom_app (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) (E : B.Modules) :
    (cmp g' π w).hom.app E =
      (Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := rfl

@[reassoc] theorem cmp_naturality (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) {E F : B.Modules} (u : E ⟶ F) :
    (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map u) ≫ (cmp g' π w).hom.app F =
      (cmp g' π w).hom.app E ≫ (Scheme.Modules.pullback g).map u :=
  (cmp g' π w).hom.naturality u

@[reassoc] theorem cmp_assoc (h : S ⟶ T) (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) {k : S ⟶ B}
    (w₂ : h ≫ g = k) {h' : S ⟶ Y} (w₁ : h ≫ g' = h') (w₃ : h' ≫ π = k) (E : B.Modules) :
    (Scheme.Modules.pullback h).map ((cmp g' π w).hom.app E) ≫ (cmp h g w₂).hom.app E =
      (cmp h g' w₁).hom.app ((Scheme.Modules.pullback π).obj E) ≫ (cmp h' π w₃).hom.app E := by
  subst w w₂ w₁
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h g' π) E
  simp [cmp, Scheme.Modules.pullbackCongr] at this ⊢
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).inv.app E ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).inv.app E))]
  simp only [Category.assoc, reassoc_of% this, eqToHom_trans, eqToHom_refl]
  simp [← Functor.map_comp_assoc]

variable {R : Type} [CommRing R] {N : ℕ} {L Q : T.Modules}

end GlobalTheory.LineQuot

end
