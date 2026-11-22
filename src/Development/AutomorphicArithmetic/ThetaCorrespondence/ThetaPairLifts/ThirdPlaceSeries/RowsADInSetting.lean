import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExponeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitPrimeHypsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherRestStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem rowsAD_in_setting_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := _root_.GlobalTheory.T.adm_at_inert_of_range hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := _root_.GlobalTheory.T.unramified_places_declared' hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := _root_.GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := _root_.GlobalTheory.splitCase_bound_at_point_of_admitted_items hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (_root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨_root_.GlobalTheory.NLink.starAD_of_global D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := _root_.GlobalTheory.NLink.BBSize.main D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (_root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h
end GlobalTheory.NLink
end
