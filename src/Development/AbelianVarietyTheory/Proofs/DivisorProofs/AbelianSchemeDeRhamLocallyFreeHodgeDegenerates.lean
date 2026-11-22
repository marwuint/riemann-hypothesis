import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham := by
  intro R _ A _ g hA hg
  obtain ⟨hfr, h0, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hg
  obtain ⟨hO, hW, hB1, -⟩ := _root_.GlobalTheory.AbCoh.oStr R A g hA hg
  have hcl := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R A g hA hg
  have hs := _root_.GlobalTheory.AbCoh.toHO1_surjective R A g hA hg
  have hH := (_root_.GlobalTheory.AbCoh.rank_prim_HH1 R A g hA hg).1
  refine ⟨⟨hH.1, hH.2.1, fun p ↦ (hH.2.2 p).trans (by push_cast; rfl)⟩,
    _root_.GlobalTheory.AbCoh.exists_wedge_hyp_equiv R _ (OAff A.hom) hfr h0 hcl hs hW (_root_.GlobalTheory.AbCoh.cupHH_self_eq_zero R A g hA hg),
    _root_.GlobalTheory.AbCoh.globForm_FP R A g hA hg, hO, ⟨hcl, ofForm_injective_of_H0Const R _ (OAff A.hom) h0, hs⟩, ?_⟩
  intro R' _ _ X' s' φ h
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ := _root_.GlobalTheory.AbCoh.baseChange_HH1_globForm R A g hA hg R' X' s' φ h
  obtain ⟨e₃, he₃⟩ := hB1 R' X' s' φ h
  refine ⟨⟨e₁, fun c ↦ ?_⟩, ⟨e₂, fun c ↦ ?_⟩, e₃, fun c ↦ ?_⟩
  · rw [he₁]; exact isPull1_pullHH1 h.w c
  · rw [he₂]; exact isPullForm_pullForm h.w c
  · rw [he₃]; exact isPullO_pullHO1 h.w c

end GlobalTheory.AbCoh
