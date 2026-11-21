import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.UniformIffAboveThreshold

open Filter Set Real

namespace KStar.Consta

structure TopParams where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  Ct : ℝ
  Ct_nonneg : 0 ≤ Ct
  Cc : ℝ
  la : ℝ
  one_lt_la : 1 < la
  q : ℕ
  q_pos : 0 < q
  R : ℕ
  CK : ℝ
  eps_le : eps ≤ 2 * CK * Ct

noncomputable instance : Inhabited TopParams :=
  ⟨{ eps := 1 / 100, eps_pos := by norm_num, eps_lt := by norm_num, Ct := 401,
     Ct_nonneg := by norm_num, Cc := 1, la := 2, one_lt_la := by norm_num, q := 1,
     q_pos := one_pos, R := 1, CK := 1, eps_le := by norm_num }⟩

namespace TopParams

end TopParams

end KStar.Consta
