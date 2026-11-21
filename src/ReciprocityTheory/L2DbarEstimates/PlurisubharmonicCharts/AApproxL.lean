import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxJ

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by
  have hloc : ∀ i y, y ∈ (A.chart i).source →
      A.nsq la u y = ‖u i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    intro i y hy
    have hg := A.g_ne la (A.pick y) i y (A.mem_pick y) hy
    have ht := A.ph_trans la (A.pick y) i y (A.mem_pick y) hy
    have hg2 : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
    have hp : A.ph la (A.pick y) y = A.ph la i y + Real.log (‖A.g la (A.pick y) i y‖ ^ 2) := by
      linarith
    unfold nsq
    rw [hcoc (A.pick y) i y (A.mem_pick y) hy, hp, norm_mul, mul_pow, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log hg2]
    field_simp
  rw [continuous_iff_continuousAt]
  intro y0
  have hy0 : y0 ∈ (A.chart (A.pick y0)).source := A.mem_pick y0
  have hs : (A.chart (A.pick y0)).source ∈ 𝓝 y0 := (A.chart (A.pick y0)).open_source.mem_nhds hy0
  have hu : ContinuousOn (u (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (hc (A.pick y0)).comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hph : ContinuousOn (A.ph la (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (A.smooth_ph la (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hf : ContinuousOn (fun y => ‖u (A.pick y0) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y0) y))
      (A.chart (A.pick y0)).source :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  exact (hf.congr fun y hy => hloc (A.pick y0) y hy).continuousAt hs

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
