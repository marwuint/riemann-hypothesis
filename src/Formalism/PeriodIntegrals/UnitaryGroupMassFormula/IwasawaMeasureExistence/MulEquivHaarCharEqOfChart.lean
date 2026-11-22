import Mathlib

noncomputable section

namespace PI.IwaMeasEx.MG

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

theorem smul_cancel {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hKx).ne'
  have htop : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K := by
    have e := congrArg (fun m : Measure Y => m K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have hab : (a : ℝ≥0∞) = b := (ENNReal.mul_left_inj h0 htop).mp hK'
  exact_mod_cast hab

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by
  have hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s)
      = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre, measure_preimage_add_right]

end PI.IwaMeasEx.MG

end
