import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawBasic

def firstRow (N : ℕ) : (Fin 1 × Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun u j := u (0, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SphereLawBasic

end

end GroundTheory.Heights₂.Heights
