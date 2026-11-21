import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GaussNormBasic

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
theorem normAbv_apply (x : L) : normAbv L x = ‖x‖ := rfl

end GaussNormBasic

end

end GroundTheory.Heights₂.Heights
