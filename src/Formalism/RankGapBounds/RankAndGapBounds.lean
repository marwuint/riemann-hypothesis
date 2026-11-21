import Mathlib

namespace Formalism.RankGapBounds.AbsolutelyIrreducibleSpan

structure Hyp (k m t r N : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  N_def : N = k + m * (t + r + 8)
  h₀_big : (t : ℝ) + 2 * (N : ℝ) ^ 3 < h₀

end Formalism.RankGapBounds.AbsolutelyIrreducibleSpan
