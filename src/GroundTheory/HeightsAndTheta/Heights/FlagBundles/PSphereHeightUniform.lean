import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

instance SphereHeightUniform.isFiniteMeasure_sphereMeasure : IsFiniteMeasure sphereMeasure := by
  unfold sphereMeasure
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
    rw [Ne, Measure.measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero _
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr h0)) (measure_lt_top _ _)

end

end GroundTheory.Heights₂.Heights.FlagBundles
