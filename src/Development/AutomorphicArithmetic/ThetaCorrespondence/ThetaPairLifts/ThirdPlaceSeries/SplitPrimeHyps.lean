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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTerStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherMoreStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherFurtherStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherExtraStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem splitPrime_hyps_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  intro Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have fa := S.facts
  have hJ : AdmissibleParameterJ.ConclusionJa D := (_root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L S.par)).1
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    rw [Nat.cast_zero]; exact (Real.exp_pos _).le
  have hL : (1 : ℝ) ≤ L.sc.L := by have := S.big; linarith
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt Pr.font Pr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 S.canon P hL le_rfl hb
    (fa.admJ L S.par) S.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG
  obtain ⟨_, _, _, _, _, _, _, hRest, hTB, hRow, _⟩ := hub
  obtain ⟨hDecl, hRam, hType, hPt, _⟩ := hRow i hTw hg hR hSp
  refine ⟨hJ.choose, hDecl hJ, hRam, ?_⟩
  intro π hπ
  have sp := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨g1, _, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, h2, cft⟩ := sp
  have hG2 := _root_.GlobalTheory.T.admG2_of_setup_jumps Pr D L P nch HW F Cm X C₂ S hJ.choose hJ.choose_spec i
  have hG5 := _root_.GlobalTheory.T.admG5_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨lc, lr⟩ := _root_.GlobalTheory.T.liftExponentColumn_and_dualPlaces Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have hH0 := _root_.GlobalTheory.T.h0_column_length_bound_of_setup Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp π hπ
  obtain ⟨sub, acont, a56⟩ := _root_.GlobalTheory.T.ambSub_ambCont_h0_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  obtain ⟨unr, dual, t2, aw, fil, h1f, a51, _⟩ := hPt π hπ
  have blk := (hRest i hg π hπ).block
  obtain ⟨M0, h0, jtb⟩ := hTB i hR π
  have tb9 : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    _root_.GlobalTheory.TBLocal.main D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (_root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D HW F Cm) (_root_.GlobalTheory.NLink.wAll_holds D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) font jtb
  have tb : EmbeddingTypes.admTB i (X.r i) π (X.dc i) (X.cB i) := fun w hw _ C hC => tb9 w hw C hC
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := _root_.GlobalTheory.BKaRows.bkaAll_of_hypotheses Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := _root_.GlobalTheory.finAll_of_localTateDuality Pr.tate D i
  exact ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, unr, cont, ss, dec, eps, tie,
    shape, font, h2, fin, cft, blk, dual, t2, aw, fil, h1f, sub, acont, hType _⟩
end GlobalTheory.NLink
end
