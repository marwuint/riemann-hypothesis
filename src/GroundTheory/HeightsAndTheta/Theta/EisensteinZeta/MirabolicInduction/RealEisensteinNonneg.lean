import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.QuadraticFieldSqrtNegSeven
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane

def realEisenstein (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

end GroundTheory.Heights₂.Theta
