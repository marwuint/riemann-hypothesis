import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAutCentre
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBoundBottomPairsNormsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantTripleCoefficient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleRootOfUnityTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaBoundVp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSumDenominatorBoundOfFactorClaims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDepthConditionsAwayFromTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsAlt
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LossOne
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Imports
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsBis
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatMove
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MatLat
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatMove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEqualSignKernelLossesBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchedFlipThetaIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningful
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypotheses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.Close

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloudIcc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem lcLeOfCloud {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem scLeB {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast (show 1 ≤ D.R.ord from D.R.ord_pos)
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

end GlobalTheory.BigTop.Fun.Close
