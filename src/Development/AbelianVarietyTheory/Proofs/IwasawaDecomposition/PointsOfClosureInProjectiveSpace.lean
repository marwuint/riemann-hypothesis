import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

variable {O : Type} [CommRing O] {N : ℕ}

end GlobalTheory.DRFlag.LineOfMap
