import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_of_adelic_integralAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  exact @GlobalTheory.RatInt.intAt_of_intAtA
