import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.RealEisensteinNonneg
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace projectiveLineClassData

open NumberField UpperHalfPlane
open scoped nonZeroDivisors

section Series

def eisTerm (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : ℝ :=
  if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

theorem realEisenstein_eq_tsum (τ : ℍ) (s : ℝ) : realEisenstein τ s = ∑' p, eisTerm τ s p := rfl

end Series

end projectiveLineClassData

end GroundTheory.Heights₂.Theta
