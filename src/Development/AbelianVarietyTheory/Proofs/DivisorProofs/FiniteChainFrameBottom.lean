import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMellin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFinMatch

theorem gBig_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

end GlobalTheory.BotFinMatch
