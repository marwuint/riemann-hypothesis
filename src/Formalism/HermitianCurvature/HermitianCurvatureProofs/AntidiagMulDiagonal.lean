import Formalism.HermitianCurvature.StatementK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText

namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K

theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
