import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaConstEqEtaWeberSqOfTripleProductStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwoStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCube
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaussianOddJacobiThetaEqDerivMulSgStar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionsRootsOfCubicOfHalfPeriodDiff

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

namespace GlobalTheory.ThetaWeberRoad

theorem jacobiProduct_of_thetaWeber {τ : UpperHalfPlane} (hTW : ThetaWeber τ)
    (hw : weberF τ * weberF₁ τ * weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ)) : JacobiProduct τ := by
  obtain ⟨h1, h2, h3⟩ := hTW
  unfold JacobiProduct
  rw [h1, h2, h3]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (ModularForm.eta (τ : ℂ)) ^ 3 *
    (weberF τ * weberF₁ τ * weberF₂ τ + ((Real.sqrt 2 : ℝ) : ℂ)) * hw +
    ModularForm.eta (τ : ℂ) ^ 3 * hs

theorem thetaWeberStatement_of (hTL : Formalism.L2.Th1.F.ThetaLine) (hSB : Formalism.L2.Th1.F.SgStarBasic)
    (hSA : Formalism.L2.Th1.F.SgStarAdd) : ThetaWeberStatement := by
  have hTW := GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct _root_.GlobalTheory.JacobiTriple.tripleProduct
  have hJ : ∀ τ : UpperHalfPlane, JacobiProduct τ := fun τ ↦
    jacobiProduct_of_thetaWeber (hTW τ) (GlobalTheory.T.weberFunction_product_eq_sqrt_two τ)
  have hH := _root_.GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of hSA (_root_.GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar hTL hSB) (_root_.GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero _root_.GlobalTheory.JacobiTriple.tripleProduct) hJ
  intro τ
  exact ⟨hH τ, hJ τ, hTW τ, _root_.GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff τ (hH τ) (hJ τ) (hTW τ)⟩

end GlobalTheory.ThetaWeberRoad
