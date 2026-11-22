import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticConductor
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace QuadraticFieldArithmetic

open NumberField Module Polynomial

section Integers

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

omit [Algebra.IsQuadraticExtension ℚ K] in

theorem isIntegral_omega (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨X ^ 2 - X + C (((d + 1) / 4 : ℕ) : ℤ), ?_, ?_⟩
  · refine Monic.add_of_left (Monic.sub_of_left (monic_X_pow 2) ?_) ?_
    · rw [degree_X, degree_X_pow]; norm_num
    · refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_sub_eq_left_of_degree_lt (by rw [degree_X, degree_X_pow]; norm_num), degree_X_pow]
      norm_num
  · rw [← aeval_def]
    have h4 : (((d + 1) / 4 : ℕ) : K) * 4 = d + 1 := by
      have e : (d + 1) / 4 * 4 = d + 1 := Nat.div_mul_cancel (by omega)
      calc (((d + 1) / 4 : ℕ) : K) * 4 = (((d + 1) / 4 * 4 : ℕ) : K) := by push_cast; ring
        _ = d + 1 := by rw [e]; push_cast; ring
    simp only [map_add, map_sub, map_pow, aeval_X, map_natCast]
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * h4

def omega (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) : 𝓞 K :=
  ⟨(1 + x) / 2, isIntegral_omega hd4 hx⟩

end Integers

end QuadraticFieldArithmetic

end GroundTheory.Heights₂.Theta
