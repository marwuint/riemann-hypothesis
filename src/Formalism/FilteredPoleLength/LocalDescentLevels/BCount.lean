import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

namespace Formalism.LatticeBaseChangeAlt

open Finset

theorem levelsSum : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring

end Formalism.LatticeBaseChangeAlt
