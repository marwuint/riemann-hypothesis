import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

end GlobalTheory.HodgeGenDesc

end
