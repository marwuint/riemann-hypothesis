import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfForallApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmThetaLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApprox
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKernelApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnQuotHeightPowMulNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleNegSpaceUnitaryElementHeq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApproxAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSeventh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulCuspIntegrableOnFst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEachStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspidalLiftSmoothAtOfCuspidalLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspTransitionRightward
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipRunDescendingCuspTransition

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
theorem cuspStep_of_large_flipRun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps hLC hP
  refine (GlobalTheory.RowClaim.Big.and (_root_.GlobalTheory.T.cusp_transition_rightward hS hP) (_root_.GlobalTheory.T.flipRun_descending_cusp_transition hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipRun_cusp_transition : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  exact @_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun
end
