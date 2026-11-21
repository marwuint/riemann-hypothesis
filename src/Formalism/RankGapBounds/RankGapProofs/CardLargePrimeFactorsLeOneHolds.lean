import Formalism.RankGapBounds.LargePrimeFactor

open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem chebyshevThetaLe_holds : ChebyshevTheta := by
  intro n
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h

end Formalism.RankGapBounds.ChebyshevFactorialBounds
