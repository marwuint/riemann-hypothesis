import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.Vert.DivPull

section Sections

variable {X Y Y' W : Scheme.{0}}

theorem pullbackComp_inv_app (b : W ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).inv.app E).app T (pullbackSections (b ≫ a) E h s) =
      pullbackSections b _ h₂ (pullbackSections a E h₁ s) := by
  have e := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)) (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at e
  refine (app_resM _ h _).trans (Eq.trans ?_ (pullbackSections_res b _ h₂ h₁ _).symm)
  exact congrArg (resM _ h) congr(($e).app U s).symm

theorem pullbackSquare_app {b : W ⟶ Y} {a : Y ⟶ X} {b' : W ⟶ Y'} {a' : Y' ⟶ X}
    (w : b ≫ a = b' ≫ a') (E : X.Modules) {U : X.Opens} {V : Y.Opens} {V' : Y'.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h₁' : V' ≤ a' ⁻¹ᵁ U) (h₂' : T ≤ b' ⁻¹ᵁ V')
    (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp b' a').symm).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections b' _ h₂' (pullbackSections a' E h₁' s) := by
  have H {j j' : W ⟶ X} (w : j = j') (h : T ≤ j ⁻¹ᵁ U) (h' : T ≤ j' ⁻¹ᵁ U) :
      ((Scheme.Modules.pullbackCongr w).hom.app E).app T (pullbackSections j E h s) =
        pullbackSections j' E h' s := by
    subst w; rfl
  have h : T ≤ (b ≫ a) ⁻¹ᵁ U := h₂.trans (b.preimage_mono h₁)
  have h' : T ≤ (b' ≫ a') ⁻¹ᵁ U := h₂'.trans (b'.preimage_mono h₁')
  rw [← pullbackComp_inv_app b a E h₁ h₂ h, ← pullbackComp_inv_app b' a' E h₁' h₂' h',
    ← H w h h']
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp b' a').symm).hom.app E =
      (Scheme.Modules.pullbackCongr w).hom.app E ≫ (Scheme.Modules.pullbackComp b' a').inv.app E := by
    simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

theorem detUnit_congr {F : X.Modules} {r : ℕ} {U U' T T' V : X.Opens} {e : Fin r → Γ(F, U)}
    {e' : Fin r → Γ(F, U')} {d : Fin r → Γ(F, T)} {d' : Fin r → Γ(F, T')} (he : IsFrame e)
    (he' : IsFrame e') (hd : IsFrame d) (hd' : IsFrame d') (h : V ≤ U) (h' : V ≤ U') (k : V ≤ T)
    (k' : V ≤ T') (H : ∀ i, resM F h (e i) = resM F k (d i))
    (H' : ∀ i, resM F h' (e' i) = resM F k' (d' i)) :
    he.detUnit he' h h' = hd.detUnit hd' k k' := by
  have e₁ : he.basis h = hd.basis k :=
    DFunLike.ext _ _ fun i => by simp only [IsFrame.basis_apply, H]
  refine Units.ext ?_
  simp only [IsFrame.val_detUnit, e₁, H']

end Sections

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z Z₁ : Model O}
  {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules} {r : ℕ}

end GlobalTheory.Vert.DivPull
