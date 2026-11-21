import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemTsupportPsiL

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv_ae (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖)
    (fun n => ((hum n).mul hI.1).add ((hvm n).mul hJ.1)) (hI.norm.add (hJ.norm.const_mul M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
  · calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · filter_upwards [hl] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn.1, hn.2]
    ring

end Lim

section Main

def psiC (n : ℕ) (c : ℂ) : ℂ := ((psiL n c : ℝ) : ℂ)

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := Complex.ofRealCLM.contDiff.comp (psiL_contDiff n)

theorem fderiv_psiC (n : ℕ) (c : ℂ) : fderiv ℝ (psiC n) c = Complex.ofRealCLM.comp (fderiv ℝ (psiL n) c) := by
  have hd : DifferentiableAt ℝ (psiL n) c := (psiL_contDiffAt n c).differentiableAt (by simp)
  exact (Complex.ofRealCLM.hasFDerivAt.comp c hd.hasFDerivAt).fderiv

theorem norm_c_dZ_psiC_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) :
    ‖c * NF.dZ (psiC n) c‖ ≤ C := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · rw [dZ_eq, fderiv_psiC, norm_mul]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hD := norm_mul_fderiv_psiL_le hC n c hc
    have ha : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm 1
    have hb : ‖((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm Complex.I
    have hz : ‖(1 / 2 : ℂ) * (((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ))‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [norm_mul]
      have h3 : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤
          2 * ‖fderiv ℝ (psiL n) c‖ := by
        calc _ ≤ ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ ‖fderiv ℝ (psiL n) c‖ + ‖fderiv ℝ (psiL n) c‖ := by
              rw [norm_mul, Complex.norm_I, one_mul]
              exact add_le_add ha hb
          _ = 2 * ‖fderiv ℝ (psiL n) c‖ := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h2]
      linarith
    calc ‖c‖ * _ ≤ ‖c‖ * ‖fderiv ℝ (psiL n) c‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ ≤ C := hD

theorem psiC_eventually (c : ℂ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, psiC n c = 1 ∧ c * NF.dZ (psiC n) c = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |Real.log ‖c‖|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlt : |Real.log ‖c‖| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev := psiL_one_near n c hc hlt
  refine ⟨?_, ?_⟩
  · simp [psiC, hev.eq_of_nhds]
  · rw [dZ_eq, fderiv_psiC, hev.fderiv_eq]
    simp

end Main

end Formalism.FourierDecayAlt.P5.HerB
