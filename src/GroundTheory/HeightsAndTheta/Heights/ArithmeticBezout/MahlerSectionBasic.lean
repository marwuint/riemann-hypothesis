import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

variable {n : ℕ}

def ballH (h : HermNorm n) : Set (Fin n → ℂ) := {v | h.norm v < 1}

def nrmv (h : HermNorm n) (v : Fin n → ℂ) : Fin n → ℂ := fun j => ((h.norm v : ℝ) : ℂ)⁻¹ * v j

end

end GroundTheory.Heights₂.Heights
