import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Imports
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMellin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStabStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GridFrameExistence

open GlobalTheory.SquareComm GlobalTheory.SquareDict GlobalTheory.SquareAgree GlobalTheory.Grid

variable {D : D7}

theorem fr_eq_of_onb {V : HSp D} {A A' : Fr V} (h : ∀ τ, A.onb τ = A'.onb τ) : A = A' := by
  have hf : A.fr = A'.fr := funext fun τ => by
    have h1 := congrArg (·⁻¹) (h τ)
    simp only [Fr.onb] at h1
    rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)),
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A'.fr_unit τ))] at h1
  have he : A.ε = A'.ε := funext fun τ => by
    have h1 : (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ = (A.fr τ)ᴴ * Formalism.REAL.Jm (A'.ε τ) * A.fr τ := by
      rw [A.fr_gram, hf, A'.fr_gram]
    have u := A.fr_unit τ
    have u' : IsUnit (A.fr τ)ᴴ := (Matrix.isUnit_conjTranspose _).2 u
    have h2 := u'.mul_left_cancel (u.mul_right_cancel h1)
    funext a
    have h3 := congrFun (congrFun h2 a) a
    cases h4 : A.ε τ a <;> cases h5 : A'.ε τ a <;> simp [Formalism.REAL.Jm, h4, h5] at h3 ⊢ <;> norm_num at h3
  cases A
  cases A'
  simp only at hf he
  subst hf he
  rfl

theorem gridFr_unique {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {X : Node} {A A' : Fr (G.V X)}
    (h : IsGridFr W X A) (h' : IsGridFr W X A') : A = A' :=
  fr_eq_of_onb fun τ => (h τ).1.trans (h' τ).1.symm

open GlobalTheory.SquareConv in

theorem standing_of_size {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hx : 11 ≤ D.host.splitBound) {T : Type}
    {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) {sc : Consts} (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  have hcc : D.host.ccK = ⊤ := hs.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hs
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

end GlobalTheory.GridFrameExistence

end
