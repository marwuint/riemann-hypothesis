import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace TorsAvgDescends

open RigSymForm

variable (P : RigSymForm ℂ)

def term (N m : ℕ) (F : P.Fn) (u v : Fin P.g → ℤ) (z : Fin P.g → ℂ) : ℂ :=
  (P.autL N u v ((m : ℂ) • z))⁻¹ * F (z + (m : ℂ)⁻¹ • P.latVec u v)

end TorsAvgDescends

open TorsAvgDescends RigSymForm

end

end GroundTheory.Heights₂.Heights.KeyFormula
