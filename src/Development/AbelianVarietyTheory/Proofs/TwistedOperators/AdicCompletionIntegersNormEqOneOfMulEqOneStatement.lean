import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F), x * y = 1 → ‖(x : Fv F v)‖ = 1 := by
  exact @GlobalTheory.adicCompletionIntegers_norm_eq_one_of_mul_eq_one
