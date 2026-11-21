import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RestPt
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockAndTorsionExponentBoundsCanonicalHubData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowPrimeOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLiveStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExponeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NSizes
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (le_trans (by norm_num) hS.big) le_rfl hb (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  obtain ⟨-, -, -, -, hCB, hC0, ⟨M0, h0', hW⟩, -⟩ := hub
  intro i hT hg hR
  refine ⟨hCB i hT hg hR, ?_, ?_⟩
  · have h := _root_.GlobalTheory.InvariantsKO.main D i (X.dc i).col (fun h => hR.1 (Or.inl h)) (fun h => hR.2.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inr h)) (fun u hu => ((X.dc i).cover u).1 (Or.inr hu))
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · intro hsp u hu
    refine ⟨hC0 i hT hg hR hsp u hu, fun π hπ => ?_⟩
    obtain ⟨hu', s, hs, hc, hcrys, hJ, hnj, hcle⟩ := hW i hT hg hsp u hu π hπ
    have hWat := _root_.GlobalTheory.NLink.wAll_holds D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
    have hHW := hWat (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) M0 h0' hcrys hJ
    have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
      M0 h0' (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) hHW hnj
    have hlen := GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent D HW i (X.ρ i) π u hu' s hs hc (X.c0 i u) _ rfl (by
      intro x hx
      have e := hkill x hx
      rw [← Nat.sub_add_cancel hcle, pow_add, mul_smul, e, smul_zero])
    have h1 := hC0 i hT hg hR hsp u hu
    have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    calc (Br.h0W i u (X.ρ i) π : ℝ) ≤ (D.R.r : ℝ) * (X.c0 i u : ℕ) := hlen
      _ ≤ (D.R.r : ℝ) * (120 * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L) := mul_le_mul_of_nonneg_left h1 hr
      _ = 120 * D.R.r * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L := by ring
end GlobalTheory.NSizes
end
