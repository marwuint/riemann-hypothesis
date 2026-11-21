import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace

lemma hlin_vsq_pos {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))

theorem perpTrace : PerpTraceStatement := by
  intro p g hg
  have hs := hlin_vsq_pos hg
  refine ⟨fun i => sub_nonneg.mpr ((div_le_one hs).mpr
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))), ?_⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - vsq g / vsq g = _
  rw [div_self hs.ne']
  simp

end ReciprocityTheory.L2DbarEstimates.H
