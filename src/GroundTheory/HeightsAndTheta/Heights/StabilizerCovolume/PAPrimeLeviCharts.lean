import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.HtBoundary
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic continuousOn_levi)

namespace APrimeLeviCharts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h1 : ContDiffAt ℝ 2 A.h z :=
    (hA.contDiffAt (isOpen_blocks.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact h1.log (A.pos z hz).ne'

theorem levi_log_h_torus {J : Type} [Fintype J] {A : HermLine ι} (hA : IsSmoothHerm A)
    {τ₁ τ₂ : (J → ℂ) → (Σ k, ι k) → ℂ} {u₀ : J → ℂ} (h₁ : AnalyticAt ℂ τ₁ u₀) (h₂ : AnalyticAt ℂ τ₂ u₀)
    (hrel : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ τ₁ u = torusSmul c (τ₂ u))
    (e : J → ℂ) :
    levi ((fun y => Real.log (A.h y)) ∘ τ₁) u₀ e = levi ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ e := by
  classical
  have hb := hrel.self_of_nhds.1
  choose i hi using hb

  set c : K → (J → ℂ) → ℂ := fun k u => τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) u₀ := fun k =>
    ((analyticAt_pi_iff.1 h₁) ⟨k, i k⟩).div ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩) (hi k)
  have hne : ∀ᶠ u in 𝓝 u₀, ∀ k, τ₂ u ⟨k, i k⟩ ≠ 0 := by
    rw [eventually_all]
    intro k
    exact ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩).continuousAt.eventually_ne (hi k)
  have hrel' : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧ (∀ k, c k u ≠ 0) ∧
      τ₁ u = torusSmul (fun k => c k u) (τ₂ u) := by
    filter_upwards [hrel, hne] with u hu hn
    obtain ⟨hbl, c', hc'0, hc'⟩ := hu
    have hcc : ∀ k, c k u = c' k := by
      intro k
      show τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ = c' k
      rw [hc']
      exact mul_div_cancel_right₀ _ (hn k)
    refine ⟨hbl, fun k => by rw [hcc]; exact hc'0 k, ?_⟩
    rw [hc']
    congr 1
    funext k
    exact (hcc k).symm
  have hc0 : ∀ k, c k u₀ ≠ 0 := hrel'.self_of_nhds.2.1

  set H : (J → ℂ) → ℂ := fun u =>
    ∑ k, ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀)) with hHdef
  have hH : AnalyticAt ℂ H u₀ := by
    have hk : ∀ k ∈ Finset.univ, AnalyticAt ℂ
        (fun u => ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀))) u₀ := by
      intro k _
      refine analyticAt_const.mul (AnalyticAt.add ?_ analyticAt_const)
      refine ((hcan k).div analyticAt_const (hc0 k)).clog ?_
      show c k u₀ / c k u₀ ∈ Complex.slitPlane
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    have hs := Finset.analyticAt_sum _ hk
    convert hs using 1
    funext u
    simp only [hHdef, Finset.sum_apply]
  have hHre : ∀ u, (∀ k, c k u ≠ 0) → (H u).re = ∑ k, (A.a k : ℝ) * Real.log ‖c k u‖ := by
    intro u hu
    simp only [hHdef, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, norm_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hc0 k))]
    ring
  have heq : ((fun y => Real.log (A.h y)) ∘ τ₁) =ᶠ[𝓝 u₀]
      fun u => ((fun y => Real.log (A.h y)) ∘ τ₂) u + 1 * (H u).re := by
    filter_upwards [hrel'] with u hu
    obtain ⟨hbl, hcu, hτ⟩ := hu
    have hs := A.smul (fun k => c k u) (τ₂ u) hcu
    have hprod : ∀ k ∈ Finset.univ, ‖c k u‖ ^ A.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (hcu k))
    simp only [Function.comp_apply, one_mul]
    rw [hHre u hcu, hτ]
    show Real.log (A.h (fun p => c p.1 u * τ₂ u p)) = _
    rw [hs, Real.log_mul (Finset.prod_ne_zero_iff.2 hprod) (A.pos _ hbl).ne', Real.log_prod hprod]
    simp only [Real.log_zpow]
    ring
  have hf : ContDiffAt ℝ 2 ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ :=
    (contDiffAt_log_h hA hrel'.self_of_nhds.1).comp u₀ h₂.restrictScalars.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun u => (H u).re) u₀ :=
    Complex.reCLM.contDiff.contDiffAt.comp u₀ hH.restrictScalars.contDiffAt
  rw [levi_congr heq, levi_add_smul 1 hf hg, levi_re_analytic hH]
  ring

section Charts

variable {P : Ideal (MRing ι)} {d : ℕ}

theorem analyticAt_sec (M : CxModel P d) {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e) {U : Set M.Xc} (hU : IsOpen U)
    {s : M.Xc → (Σ k, ι k) → ℂ} (hs : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    AnalyticAt ℂ (fun u => s (e.symm u)) u := by
  obtain ⟨j, hj⟩ := M.atlas.cover (e.symm u)
  set V : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' (U ∩ (M.atlas.chart j).source) with hV
  have hVo : IsOpen V := e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (hU.inter (M.atlas.chart j).open_source)
  have huV : u ∈ V := ⟨hu, huU, hj⟩
  refine analyticAt_pi_iff.2 fun p => ?_
  have h1 : AnalyticAt ℂ (M.atlas.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (M.atlas.chart j).symm) ((M.atlas.chart j ∘ e.symm) u) := by
    refine hs p j _ ⟨(M.atlas.chart j).map_source hj, ?_⟩
    show (M.atlas.chart j).symm ((M.atlas.chart j) (e.symm u)) ∈ U
    rw [(M.atlas.chart j).left_inv hj]
    exact huU
  refine (h2.comp h1).congr ?_
  filter_upwards [hVo.mem_nhds huV] with u' hu'
  simp only [Function.comp_apply]
  rw [(M.atlas.chart j).left_inv hu'.2.2]

end Charts

end APrimeLeviCharts

end GroundTheory.Heights₂.Heights.NineStatements
