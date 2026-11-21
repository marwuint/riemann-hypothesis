import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.IsIntegralVecCoordsOfRatCoordsSingle

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

section Arithmetic

variable {K : Type*} [Field K] [NumberField K]

theorem exists_int_trace_eq {t : K} (ht : IsIntegral ℤ t) : ∃ n : ℤ, Algebra.trace ℚ K t = n :=
  ⟨Algebra.trace ℤ (𝓞 K) ⟨t, ht⟩, (Algebra.coe_trace_int (K := K) ⟨t, ht⟩).symm⟩

theorem exists_int_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ t : K, (∀ s, ∃ n : ℤ, Algebra.trace ℚ K (t * integralBasis K s) = n) →
      IsIntegral ℤ ((D : K) * t) := by
  classical
  let B := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral (Finset.univ.image fun s => B s)
  refine ⟨D, hD0, fun t ht => ?_⟩
  have hexp : t = ∑ s, (Algebra.trace ℚ K (t * integralBasis K s) : K) * B s := by
    conv_lhs => rw [← B.sum_repr t]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Rat.smul_def]
  rw [hexp, Finset.mul_sum]
  refine IsIntegral.sum _ fun s _ => ?_
  obtain ⟨n, hn⟩ := ht s
  rw [hn, Rat.cast_intCast, mul_left_comm]
  exact (isIntegral_algebraMap (x := n)).mul (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

end Arithmetic

end GroundTheory.Automorphic
