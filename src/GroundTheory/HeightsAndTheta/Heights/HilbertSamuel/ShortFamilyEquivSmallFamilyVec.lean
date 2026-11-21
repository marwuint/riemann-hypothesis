import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem fibreNorm_one_tmul (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (v : E.carrier) :
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) = ‖fibreVec E.metric σ v‖ :=
  rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
