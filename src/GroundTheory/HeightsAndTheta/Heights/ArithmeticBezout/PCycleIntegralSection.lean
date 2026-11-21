import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem cycleIntegral_eq_sum {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := rfl

end

end GroundTheory.Heights₂.Heights
