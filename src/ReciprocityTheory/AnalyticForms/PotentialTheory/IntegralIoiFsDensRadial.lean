import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm

open MeasureTheory Filter Topology Set

noncomputable section

def fsDens (z : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)

theorem integral_Ioi_fsDens_radial :
    ∫ r in Ioi (0 : ℝ), r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)) = 1 / (2 * Real.pi) := by
  have hπ := Real.pi_pos
  have key := integral_Ioi_of_hasDerivAt_of_nonneg (a := 0) (l := 0)
    (g := fun r : ℝ => -(2 * Real.pi * (1 + r ^ 2))⁻¹)
    (g' := fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)))
    (by fun_prop (disch := positivity)) ?_ ?_ ?_
  · rw [key]; simp
  · intro r _
    have h1 : (2 * Real.pi * (1 + r ^ 2)) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' r).pow 2).const_add 1).const_mul (2 * Real.pi)).inv h1 |>.neg
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  · intro r hr
    have : (0 : ℝ) < r := hr
    positivity
  · have h1 : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + r ^ 2)) atTop atTop := by
      apply Tendsto.const_mul_atTop (by positivity)
      exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp h1).neg

theorem integral_fsDens : ∫ z : ℂ, fsDens z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hf : ∀ p : ℝ × ℝ, p.1 • fsDens (Complex.polarCoord.symm p) =
      p.1 * (1 / (Real.pi * (1 + p.1 ^ 2) ^ 2)) * 1 := by
    intro p
    simp [fsDens, sq_abs]
  simp_rw [hf]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) (fun _ => (1 : ℝ)),
    integral_Ioi_fsDens_radial]
  have hπ := Real.pi_pos
  rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by linarith)]
  simp
  field_simp
  ring

theorem integrable_fsDens : Integrable fsDens :=
  .of_integral_ne_zero (by rw [integral_fsDens]; exact one_ne_zero)

end

end ReciprocityTheory.AnForm
