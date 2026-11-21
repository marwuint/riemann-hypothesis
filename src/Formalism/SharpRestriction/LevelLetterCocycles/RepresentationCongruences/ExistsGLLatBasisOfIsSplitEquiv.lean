import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTA

open PowerSeries

variable {O : Type*} [CommRing O]

theorem alg_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  have e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a := by
    first
    | rfl
    | simp
    | (rw [PowerSeries.algebraMap_apply']; rfl)
  rw [e, AlgHom.commutes]

private theorem exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one (l : ℕ) (x y : O⟦X⟧)
    (hx : constantCoeff x = 1) (hy : constantCoeff y = 1) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ x ^ l - y ^ l = S * (x - y) := by
  refine ⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩
  · simp [map_sum, hx, hy]
  · first
    | exact (geom_sum₂_mul x y l).symm
    | exact ((Commute.all x y).geom_sum₂_mul l).symm

theorem exists_GL_latBasis_of_isSplitEquiv (l : ℕ) :
    ∃ Q0 : O⟦X⟧, constantCoeff Q0 = l ∧ (1 + X : O⟦X⟧) ^ l - 1 = X * Q0 := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)
  exact ⟨S, hS, by linear_combination e⟩

variable [IsDomain O] [CharZero O]

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTA
