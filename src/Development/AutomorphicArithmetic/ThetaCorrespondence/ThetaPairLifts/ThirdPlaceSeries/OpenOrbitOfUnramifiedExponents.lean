import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePack
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPinsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownward
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BkLawEntries
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntriesCombinedReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombined
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombined
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessPlacesEqImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstructedAfterLargeBaseCorePropertyOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWbStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinkedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinLinkedRealizationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtHDivGOfMiStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealGroupInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HarishChandraInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesGoodOfLocalLanglands
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLabOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0AtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointEvaluationSideStatement

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.S0.Open0ProofU
theorem open_orbit_of_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := _root_.GlobalTheory.T.linkedAt_hPA_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := _root_.GlobalTheory.T.linkedAt_tie_of_nonempty_extensionWithLaw P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := _root_.GlobalTheory.T.entries_combined_real_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := _root_.GlobalTheory.T.bk_law_entries_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := _root_.GlobalTheory.T.good_ft_entries_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie P.rayClassFieldSt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := _root_.GlobalTheory.T.weil_unitary_entries' P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩
end GlobalTheory.Fc.S0.Open0ProofU
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt
end
end
