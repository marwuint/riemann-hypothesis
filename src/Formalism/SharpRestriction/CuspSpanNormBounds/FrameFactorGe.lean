import Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {r : ℕ} {κ τ : ℝ}

theorem frames_ineqs {pw pw₁ s K ρ F : ℝ} (X : ENNReal) (hs : 0 ≤ s) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (h1 : ρ ≤ F) (h2 : ρ⁻¹ ≤ F) (he : pw₁ * s = K * ρ * pw) :
    ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X) ≤ ENNReal.ofReal (K * F) * (ENNReal.ofReal pw * X) ∧
      ENNReal.ofReal K * (ENNReal.ofReal pw * X) ≤ ENNReal.ofReal F * (ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X)) := by
  have hF : 0 < F := lt_of_lt_of_le hρ h1
  rw [← mul_assoc (ENNReal.ofReal pw₁), ← ENNReal.ofReal_mul' hs, he]
  by_cases hp : pw ≤ 0
  · have h0 : K * ρ * pw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hρ.le) hp
    rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos hp]
    simp
  · push Not at hp
    constructor
    · rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK hF.le)]
      gcongr ENNReal.ofReal ?_ * _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hp.le
    · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hF.le]
      gcongr ENNReal.ofReal ?_ * _
      have : 1 ≤ F * ρ := by
        have := mul_le_mul_of_nonneg_right h2 hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at this
      nlinarith [mul_nonneg hK hp.le]

end Formalism.MainNotions.FrameBoundFromBesselTorus
