import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Cuspidal

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem continuous_vadd_upperHalfPlane (z : ℍ) : Continuous fun t : ℝ => t +ᵥ z := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_
  have : ((↑) ∘ fun t : ℝ => t +ᵥ z) = fun t : ℝ => (t : ℂ) + (z : ℂ) := by
    funext t
    simp only [Function.comp_apply, coe_vadd]
  rw [this]
  fun_prop

theorem periodic_comp_ofComplex_of_vadd {F : ℍ → ℂ} {M : ℝ} (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) :
    Function.Periodic (F ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push Not at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem tendsto_atImInfty_of_periodic_of_mdifferentiable {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) :
    Tendsto F atImInfty (𝓝 (cuspFunction M F 0)) := by
  have hfper := periodic_comp_ofComplex_of_vadd hper
  have han := analyticAt_cuspFunction_zero hM hfper hhol hbdd
  have e : (cuspFunction M F ∘ fun τ : ℍ => Function.Periodic.qParam M τ) = F := by
    funext τ
    simpa using eq_cuspFunction τ hM.ne' hfper
  simpa [e] using han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hM)

theorem isZeroAtImInfty_of_integral_vadd_eq_zero {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F)
    (hint : ∀ z : ℍ, ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0) : IsZeroAtImInfty F := by
  set c := cuspFunction M F 0
  have ht := tendsto_atImInfty_of_periodic_of_mdifferentiable hM hper hhol hbdd
  suffices hc : c = 0 by
    rw [IsZeroAtImInfty, ZeroAtFilter, ← hc]
    exact ht
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (ht.eventually (Metric.closedBall_mem_nhds c hε))
  have hY : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z₀ : ℍ := ⟨(max A 1 : ℝ) * Complex.I, by simp [hY]⟩
  have hbound : ∀ t : ℝ, ‖F (t +ᵥ z₀) - c‖ ≤ ε := by
    intro t
    have hz : A ≤ (t +ᵥ z₀).im := by
      rw [vadd_im]
      show A ≤ ((max A 1 : ℝ) * Complex.I).im
      simp
    have := hA _ hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hcont : Continuous fun t : ℝ => F (t +ᵥ z₀) :=
    hhol.continuous.comp (continuous_vadd_upperHalfPlane z₀)
  have hint' : ∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c) = -(M • c) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const, hint z₀,
      intervalIntegral.integral_const, sub_zero, zero_sub]
  have hle : ‖∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c)‖ ≤ ε * |M - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hbound t
  rw [hint', norm_neg, norm_smul, Real.norm_eq_abs, sub_zero, abs_of_pos hM] at hle
  exact le_of_mul_le_mul_left (by linarith [hle] : M * ‖c‖ ≤ M * ε) hM

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem isBoundedAtImInfty_slash_toReal (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    refine ⟨δ • OnePoint.infty, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]
    rfl
  exact f.bdd_at_cusps' hc (toReal δ) rfl

end GL2Classical

end

end GroundTheory.Automorphic
