import Mathlib

open MeasureTheory in
theorem UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      MeasurePreserving (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) volume volume := by
  intro ι κ _ _
  have hm : Measurable (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) :=
    measurable_pi_lambda _ fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq (μ := fun _ : ι × κ ↦ (volume : Measure ℝ)) ?_
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall,
      Function.uncurry_apply_pair]
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [volume_pi_pi]
