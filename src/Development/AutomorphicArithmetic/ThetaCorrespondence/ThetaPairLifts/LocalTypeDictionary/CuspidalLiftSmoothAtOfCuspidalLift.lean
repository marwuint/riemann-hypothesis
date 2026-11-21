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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaKernelMulCuspFormIntegrableOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralIntegrableOnAutomorphicQuotient
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaIntegralConverges
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaIntegralIntegrableOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardThetaLiftIsCuspidalOfIntegrable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnConvolutionIntegrableOnSlice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsCuspidalOfDefinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftHasTypeAtPlaces

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspSmoothLift
theorem cuspidal_lift_smooth_at_of_cuspidal_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_integral_integrableOn_automorphic_quotient hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_upward_theta_integral_converges hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro t j hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.columnConvolution_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.columnLift_isAutomorphicFunction hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_isCuspForm hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc⟩
end GlobalTheory.CuspSmoothLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  first | exact @_root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | exact _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | (intros; apply _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift <;> assumption)
end
