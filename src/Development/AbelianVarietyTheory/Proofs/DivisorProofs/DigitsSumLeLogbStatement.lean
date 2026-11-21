import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  exact @GlobalTheory.digits_sum_le_logb
