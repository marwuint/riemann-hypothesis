import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  exact @GlobalTheory.PullbackForm.isForm_pullback
