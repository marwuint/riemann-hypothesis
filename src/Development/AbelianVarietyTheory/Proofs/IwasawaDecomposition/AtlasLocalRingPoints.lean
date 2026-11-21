import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.Spez

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Flags

variable {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_bc (φ : R →+* S) {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (h : SameFlag ty t x u u') :
    SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ) := fun σ j hj i hi => by
  obtain ⟨cf, h1, h2⟩ := h σ j hj i hi
  exact ⟨fun l => φ (cf l), fun l hl => by simp [h1 l hl], comb_bc φ h2⟩

theorem sameFlag_of_bc {l : Level H} {c : Coeff l} {g : c.F →+* R} {φ : R →+* S} (hφ : Function.Injective φ)
    {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (hu : LocM.IsFrame t g x u) (hu' : LocM.IsFrame t g x u')
    (h : SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ)) : SameFlag ty t x u u' := fun σ j hj i hi => by
  obtain ⟨cf, hcf, -⟩ := hu.exists_comb hu' σ i
  obtain ⟨cf', h1, h2⟩ := h σ j hj i hi
  have e := ((GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu).exists_comb
    (GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu') σ i).unique (comb_bc φ hcf) h2
  exact ⟨cf, fun m hm => hφ ((congrFun e m).trans ((h1 m hm).trans (map_zero φ).symm)), hcf⟩

end Flags

end GlobalTheory.DRFlag.Spez
