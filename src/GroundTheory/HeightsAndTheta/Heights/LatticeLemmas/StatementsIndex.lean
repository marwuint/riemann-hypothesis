import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

section Scale

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def localScalar (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) : v.adicCompletion K :=
  (algebraMap (𝓞 K) (v.adicCompletionIntegers K) b : v.adicCompletion K)

theorem localScalar_eq (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    localScalar v b = FinitePlace.embedding v (b : K) := rfl

end Scale

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
