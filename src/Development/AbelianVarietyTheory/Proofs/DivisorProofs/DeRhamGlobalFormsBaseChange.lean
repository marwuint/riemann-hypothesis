import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1Surjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exact_clAll_toHO1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hc : Closed1 (OAff s) = ⊤) :
    Function.Exact (clAll (OAff s) hc) (toHO1 s) := by
  rw [LinearMap.exact_iff]
  change Fil1 (OAff s) = _
  rw [Fil1_eq_range, clAll, LinearMap.range_comp_of_range_eq_top]
  exact LinearEquiv.range _

theorem surjective_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) : Surjective f := by
  have : Surjective (e ≫ f) := by rw [he]; infer_instance
  exact Surjective.of_comp e f

theorem baseChange_HH1_globForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R _ A _ g hab hsm R' _ _ X' s' φ h
  obtain ⟨inst', hab', hsm'⟩ := _root_.GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap R A g hab hsm R' (algebraMap R R') X' s' φ h
  obtain ⟨hfr, h0, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hab hsm
  obtain ⟨hfr', h0', -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R' (Over.mk s') g hab' hsm'
  have hc := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R A g hab hsm
  have hc' := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R' (Over.mk s') g hab' hsm'
  have hflat : Flat s' := by
    haveI := hsm'
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth g s'
    infer_instance
  have hsurj : Surjective s' := by
    refine surjective_of_section s' (η[Over.mk s']).left ?_
    have := Over.w (η[Over.mk s'])
    simpa using this
  have hW := _root_.GlobalTheory.AbCoh.exists_equiv_globForm_baseChange R R' A.left X' A.hom s' φ h hfr h0 hfr' h0' hflat hsurj
  refine ⟨?_, hW⟩
  have hH := (_root_.GlobalTheory.AbCoh.oStr R A g hab hsm).2.2.1 R' X' s' φ h
  refine _root_.GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact R R' (GlobForm A.hom) (HH1 A.hom) (HO1 A.hom) (GlobForm s') (HH1 s') (HO1 s')
    (clAll (OAff A.hom) hc) (toHO1 A.hom) (clAll (OAff s') hc') (toHO1 s')
    (pullForm h.w) (pullHH1 h.w) (pullHO1 h.w)
    (_root_.GlobalTheory.AbCoh.toHO1_surjective R A g hab hsm) (exact_clAll_toHO1 A.hom hc) ?_ (exact_clAll_toHO1 s' hc') ?_ ?_ hW hH
  · exact (ofForm_injective_of_H0Const R' _ (OAff s') h0').comp (LinearEquiv.injective _)
  · intro x
    exact _root_.GlobalTheory.AbCoh.pullHH1_clAll R R' A.left X' A.hom s' (algebraMap R R') φ h.w hc hc' x
  · intro x
    exact toHO1_pullHH1 h.w x

end GlobalTheory.AbCoh
