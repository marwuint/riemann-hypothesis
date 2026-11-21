import Mathlib

namespace PI.Residue

open NumberField
open scoped ENNReal NNReal

noncomputable def wt (s : ℝ) : ℕ →* ℝ≥0∞ where
  toFun n := (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞)
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, NNReal.mul_rpow, ENNReal.coe_mul]

theorem wt_apply (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := rfl

end PI.Residue
