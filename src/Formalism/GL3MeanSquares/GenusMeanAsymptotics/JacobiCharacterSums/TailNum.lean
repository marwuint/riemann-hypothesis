import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ 398 := by positivity
  have hp1 : 1 ≤ x ^ 398 := one_le_pow₀ hx1
  have hA : x ^ 400 + x ^ 400 * (1 / x ^ 2) = x ^ 398 * (x ^ 2 + 1) := by
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hA1 : x ^ 398 * (x ^ 2 + 1) ≤ x ^ 401 := by
    have : x ^ 401 = x ^ 398 * x ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq hp.le
  have hApos : 0 < x ^ 398 * (x ^ 2 + 1) := by positivity
  have hAge : 1 ≤ x ^ 398 * (x ^ 2 + 1) := by nlinarith
  have hL0 : 0 ≤ Real.log (x ^ 398 * (x ^ 2 + 1)) := Real.log_nonneg hAge
  have hL1 : Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ 401 * x := by
    calc Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ Real.log (x ^ 401) := Real.log_le_log hApos hA1
      _ = 401 * Real.log x := by rw [Real.log_pow]; norm_num
      _ ≤ 401 * x := by
        have := Real.log_le_sub_one_of_pos hx0
        linarith
  have hx399 : x ≤ x ^ 399 := by
    have : x ^ 399 = x * x ^ 398 := by ring
    rw [this]
    nlinarith
  rw [hA, div_le_iff₀ (by positivity : (0:ℝ) < x ^ 399)]
  calc (x ^ 398 + 1) * Real.log (x ^ 398 * (x ^ 2 + 1))
      ≤ (x ^ 398 + 1) * (401 * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 401 * x ^ 399 + 401 * x := by ring
    _ ≤ 802 * x ^ 399 := by linarith

end Formalism.HermitianLattices.Ext.BoxTail
