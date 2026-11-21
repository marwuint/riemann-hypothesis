import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLatticeNested
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFrameChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertSamuelProjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricToFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjectiveBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSMBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopPullFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsArithVarNoBlocks
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem TheoremHSMBlock.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionImageSup.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegreeIntegral.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement)
    (h13 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h14 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.Statement)
    (h15 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h16 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphDeg.Statement)
    (h17 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h18 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjectiveBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMetricChange.proof BlockMeasureChange.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockDefectMetricChange.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockRealGramComparison.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionSupBound.proof h10 NonvanishingDense.full) SupBoundBlock.full
  SupBoundCount.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockComplexGramMetricChange.proof MetricChange.full
  BlockResolutionMetricPair.full BlockResolutionFormsIndependent.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegree.proof BlockSectionsRank.full h11))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof h12 BlockResolutionInterpIntegral.full)
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h13 Closed.PtsSumMeasurable)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageDatum.proof BlockImageArith.full h14 AnResNullForm.full
  BlockImageMetrics.full BlockImageChi.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageTop.proof h15
  BlockGraphImage.full h16) BlockImageGenDeg.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h17)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h15 VeroneseArith.full VeroneseGraphImage.full h18)
  VeroneseGenDeg.full) PointHeightFS.full) SupBoundBlock.full)

end GroundTheory.Heights₂.Heights.HilbertSamuel
