import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplexStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := _root_.GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := _root_.GlobalTheory.FrobStick.colAB_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := _root_.GlobalTheory.FrobStick.colC_atU _root_.GlobalTheory.DerivTransport.atU_deriv p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex p g.lam _ (sgStar g.abelian₂) hF hσ (_root_.GlobalTheory.FrobStick.tay_defect_eq_zero _root_.GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines _root_.GlobalTheory.FrobStick.defect_line _root_.GlobalTheory.FrobStick.sgStar_cube_det_cplx g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := _root_.GlobalTheory.FrobStick.SubstLog.subst_log_formula p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine _root_.GlobalTheory.FrobStick.det_column_ops p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
