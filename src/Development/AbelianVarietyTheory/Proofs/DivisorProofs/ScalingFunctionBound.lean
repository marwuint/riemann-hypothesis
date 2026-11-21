import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

noncomputable section

open Filter Asymptotics

namespace GlobalTheory.BigTop.Fun

theorem exists_log_le_two_rpow {eps : ℝ} (he : 0 < eps) : ∃ x0 : ℝ, ∀ y, x0 ≤ y → Real.log y ≤ 2 * y ^ eps := by
  have hev : ∀ᶠ y in atTop, Real.log y ≤ 2 * y ^ eps := by
    have h := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 2)
    filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
    exact (le_abs_self _).trans hy
  exact eventually_atTop.1 hev

end GlobalTheory.BigTop.Fun

end
