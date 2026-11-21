import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.KGauge

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

end Trotter

end PI.IwaMeasEx.Gauge.ZetaZeros

end
