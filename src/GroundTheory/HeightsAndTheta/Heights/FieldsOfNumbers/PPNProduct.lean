import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

section Product

variable {K : Type}

def diff1 (g : ℤ → ℤ) : ℤ → ℤ := fun t => g t - g (t - 1)

end Product

end

end GroundTheory.Heights₂.Heights.FieldNumbers
