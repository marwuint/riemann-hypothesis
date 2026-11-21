import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem gaap_measurableSet_pts {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    MeasurableSet (pts P) := by
  have : pts P = ({0}ᶜ : Set (J → ℂ)) ∩
      ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
    ext z
    simp [pts, conePts]
  rw [this]
  refine (measurableSet_singleton 0).compl.inter (IsClosed.measurableSet ?_)
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

theorem gaap_mem_ball_add {y₀ y : Fin D → ℂ} {ρ₀ : ℝ} :
    y₀ + y ∈ Metric.ball y₀ ρ₀ ↔ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ := by
  simp [Metric.mem_ball, dist_eq_norm]

theorem IsParam.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (h : IsParam P U γ) (y₀ : Fin D → ℂ) {ρ₀ : ℝ}
    (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsParam P (Metric.ball 0 ρ₀) fun y => γ (y₀ + y) := by
  obtain ⟨_, hd, hpts, O, q, hO, hq, hOeq, hsc, hqγ⟩ := h
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  refine ⟨Metric.isOpen_ball, ?_, fun y hy => hpts _ (hmaps y hy),
    O ∩ q ⁻¹' Metric.ball y₀ ρ₀, fun z => q z - y₀,
    hq.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball,
    (hq.mono Set.inter_subset_left).sub analyticOnNhd_const, ?_, ?_, ?_⟩
  · exact hd.comp (analyticOnNhd_const.add analyticOnNhd_id) fun y hy => hmaps y hy
  · ext z
    constructor
    · rintro ⟨⟨hzO, hzq⟩, hzp⟩
      have hz : z ∈ coneOver U γ := hOeq ▸ ⟨hzO, hzp⟩
      obtain ⟨y, hyU, c, hc, rfl⟩ := hz
      have h1 : q (c • γ y) = y := by rw [(hsc _ (hγO y hyU) c hc).2, hqγ y hyU]
      have hy : y ∈ Metric.ball y₀ ρ₀ := by
        have := hzq
        simp only [Set.mem_preimage, h1] at this
        exact this
      refine ⟨y - y₀, ?_, c, hc, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
    · rintro ⟨y, hy, c, hc, rfl⟩
      have hcone : c • γ (y₀ + y) ∈ coneOver U γ := ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
      rw [← hOeq] at hcone
      refine ⟨⟨hcone.1, ?_⟩, hcone.2⟩
      simp only [Set.mem_preimage]
      rw [(hsc _ (hγO _ (hmaps y hy)) c hc).2, hqγ _ (hmaps y hy)]
      exact gaap_mem_ball_add.2 hy
  · rintro z ⟨hzO, hzq⟩ c hc
    have := hsc z hzO c hc
    refine ⟨⟨this.1, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, this.2]
      exact hzq
    · simp only [this.2]
  · intro y hy
    simp only
    rw [hqγ _ (hmaps y hy), add_sub_cancel_left]

theorem gaap_setLIntegral_translate (y₀ : Fin D → ℂ) (ρ₀ : ℝ) (F : (Fin D → ℂ) → ENNReal) :
    ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ρ₀, F (y₀ + y) = ∫⁻ y in Metric.ball y₀ ρ₀, F y := by
  have hpre : (fun y => y₀ + y) ⁻¹' Metric.ball y₀ ρ₀ = Metric.ball (0 : Fin D → ℂ) ρ₀ := by
    ext y
    exact gaap_mem_ball_add
  rw [← hpre]
  exact (measurePreserving_add_left volume y₀).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft y₀) F _

theorem IsDensityFor.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {μ : Measure (Ix κ → ℂ)}
    {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) (y₀ : Fin D → ℂ) {ρ₀ : ℝ} (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsDensityFor μ (Metric.ball 0 ρ₀) (fun y => γ (y₀ + y)) fun y => ν (y₀ + y) := by
  obtain ⟨hνc, hνpos, hνint⟩ := hν
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  refine ⟨hνc.comp (contDiffOn_const.add contDiffOn_id) (fun y hy => hmaps y hy),
    fun y hy => hνpos _ (hmaps y hy), ?_⟩
  intro g hg hg0 hgnn
  obtain ⟨_, _, _, O', q', hO', -, hO'eq, -, -⟩ := h.translate y₀ hball
  obtain ⟨hU, _, _, O, q, _, _, hOeq, hsc, hqγ⟩ := h
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  set S := coneOver (Metric.ball (0 : Fin D → ℂ) ρ₀) (fun y => γ (y₀ + y)) with hSdef
  have hSm : MeasurableSet S := by
    rw [← hO'eq]
    exact hO'.measurableSet.inter (gaap_measurableSet_pts P)
  have hSsub : S ⊆ coneOver U γ := by
    rintro z ⟨y, hy, c, hc, rfl⟩
    exact ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
  have hSsmul : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ S ↔ z ∈ S) := by
    intro c z hc
    constructor
    · rintro ⟨y, hy, c', hc', he⟩
      refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
      rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rintro ⟨y, hy, c', hc', rfl⟩
      exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩
  have hγS : ∀ y ∈ U, (γ y ∈ S ↔ y ∈ Metric.ball y₀ ρ₀) := by
    intro y hyU
    constructor
    · rintro ⟨y', hy', c, hc, he⟩
      have h1 : q (γ y) = y₀ + y' := by
        rw [he, (hsc _ (hγO _ (hmaps y' hy')) c hc).2, hqγ _ (hmaps y' hy')]
      rw [hqγ y hyU] at h1
      rw [h1]
      exact gaap_mem_ball_add.2 hy'
    · intro hy
      refine ⟨y - y₀, ?_, 1, one_ne_zero, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
  have key := hνint (S.indicator g) (hg.indicator hSm)
    (fun c z hc => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hSsmul c z hc).2 hz), hg0 c z hc]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hSsmul c z hc).1 h'))])
    (fun z => Set.indicator_nonneg (fun z _ => hgnn z) z)
  have hL : ∫⁻ z in coneOver U γ, ENNReal.ofReal (S.indicator g z) ∂μ =
      ∫⁻ z in S, ENNReal.ofReal (g z) ∂μ := by
    have : (fun z => ENNReal.ofReal (S.indicator g z)) = S.indicator (fun z => ENNReal.ofReal (g z)) := by
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [this, setLIntegral_indicator hSm, Set.inter_eq_left.2 hSsub]
  have hR : ∫⁻ y in U, ENNReal.ofReal (S.indicator g (γ y) * ν y) =
      ∫⁻ y in Metric.ball y₀ ρ₀, ENNReal.ofReal (g (γ y) * ν y) := by
    rw [← Set.inter_eq_left.2 hball, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
    refine setLIntegral_congr_fun hU.measurableSet (fun y hyU => ?_)
    by_cases hy : y ∈ Metric.ball y₀ ρ₀
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hγS y hyU).2 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h' => hy ((hγS y hyU).1 h'))]
      simp
  rw [← hL, key, hR]
  exact (gaap_setLIntegral_translate y₀ ρ₀ (fun y => ENNReal.ofReal (g (γ y) * ν y))).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
