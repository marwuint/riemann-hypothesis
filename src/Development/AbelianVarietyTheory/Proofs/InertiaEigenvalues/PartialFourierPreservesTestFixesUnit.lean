import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadratic

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := _root_.GlobalTheory.trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨_root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf (_root_.GlobalTheory.isTest_nhds_inv _ f' hf), _root_.GlobalTheory.JR.fourG_hasCompactSupport F E r M ψ hψ f' hf (_root_.GlobalTheory.isTest_nhds_inv _ f' hf)⟩,
    fun f hf => ⟨_root_.GlobalTheory.fourU_isLocallyConstant F E r M ψ hψ htr f hf (_root_.GlobalTheory.isTest_nhds_inv _ f hf), _root_.GlobalTheory.fourU_hasCompactSupport F E r M ψ hψ htr f hf (_root_.GlobalTheory.isTest_nhds_inv _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, _root_.GlobalTheory.JR.fourG_unitG F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (_root_.GlobalTheory.TraceUnit.exists_trace_unit F E htr)⟩

end GlobalTheory
