import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ToricTorsionSecUnif

section FinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.toPre.P k hk
    have h₁' : IsFinite (𝟙 D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

end FinitePart

end GlobalTheory.ToricTorsionSecUnif
