import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]

def chartPartMeasure (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (s : ℝ) (j : Fin A.n) : Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))).map (A.chart j).symm

theorem chart_weight_compact [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    IsCompact ((A.chart j) '' tsupport (P.χ j)) ∧
      (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target ∧
      ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (P.χ j) →
        P.χ j ((A.chart j).symm y) = 0 := by
  have hK : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
  have hsrc := P.tsupport_subset j
  refine ⟨hK.image_of_continuousOn ((A.chart j).continuousOn.mono hsrc), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsrc hx)
  · intro y hy hy'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hy' ⟨_, h, (A.chart j).right_inv hy⟩

private theorem chiCont (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  have h := ((P.smooth j) j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact h

theorem isFiniteMeasure_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    IsFiniteMeasure (chartPartMeasure A P Φ s j) := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hi : IntegrableOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
    refine IntegrableOn.of_forall_diff_eq_zero ((hw.mono hCT).integrableOn_compact hC)
      (A.chart j).open_target.measurableSet ?_
    intro y hy
    simp [hz y hy.1 hy.2]
  unfold chartPartMeasure
  haveI : IsFiniteMeasure ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  infer_instance

private theorem integrableOn_part [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hL := hgi j _ hCT hC
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hcont : ContinuousOn (fun y => max (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y)) 0) (A.chart j).target :=
    fun y hy => (hw y hy).max continuousWithinAt_const
  have hsymm : AEMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict
      ((A.chart j) '' tsupport (P.χ j))) :=
    hg.comp_aemeasurable (((A.chart j).continuousOn_symm.mono hCT).aemeasurable hC.measurableSet)
  have hχ1 : ∀ x, P.χ j x ≤ 1 := fun x => by
    rw [← P.sum_eq_one x]
    exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)
  have hCi : IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0)
      ((A.chart j) '' tsupport (P.χ j)) := by
    refine (hL.norm.const_mul |s|).mono'
      (hsymm.mul ((hcont.mono hCT).aemeasurable hC.measurableSet)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := P.nonneg j ((A.chart j).symm y)
    have h1 := hχ1 ((A.chart j).symm y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have hm : |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0| ≤
        |s| * |locDens A Φ j y| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)
          ≤ |s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)| := le_abs_self _
        _ = |s| * (P.χ j ((A.chart j).symm y) * |locDens A Φ j y|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
        _ ≤ |s| * (1 * |locDens A Φ j y|) := by gcongr
        _ = |s| * |locDens A Φ j y| := by ring
    calc |g ((A.chart j).symm y)| * |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0|
        ≤ |g ((A.chart j).symm y)| * (|s| * |locDens A Φ j y|) := by gcongr
      _ = |s| * (|g ((A.chart j).symm y)| * |locDens A Φ j y|) := by ring
  refine IntegrableOn.of_forall_diff_eq_zero hCi (A.chart j).open_target.measurableSet ?_
  intro y hy
  simp [hz y hy.1 hy.2]

theorem integral_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (chartPartMeasure A P Φ s j) ∧
      ∫ x, g x ∂chartPartMeasure A P Φ s j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
  have hT := (A.chart j).open_target.measurableSet
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hf : AEMeasurable (fun y => (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).toNNReal)
      (volume.restrict (A.chart j).target) := (hw.aemeasurable hT).real_toNNReal
  have hsy : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    ((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac (withDensity_absolutelyContinuous _ _)
  have hgm : AEStronglyMeasurable g (chartPartMeasure A P Φ s j) := hg.aestronglyMeasurable
  have hpart := integrableOn_part A P Φ hΦ s j g hg hgi
  unfold chartPartMeasure at hgm ⊢
  constructor
  · rw [integrable_map_measure hgm hsy]
    refine (integrable_withDensity_iff_integrable_smul₀ hf).2 ?_
    refine hpart.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring
  · rw [integral_map hsy hgm]
    refine (integral_withDensity_eq_integral_smul₀ hf (fun y => g ((A.chart j).symm y))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring

end

end ReciprocityTheory.AnForm.M
