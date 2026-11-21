import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact EigFrame.exists_baseChange E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

end GlobalTheory.ShFam.ValCoord
