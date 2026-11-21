import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace GlobalTheory

section Exp

open NormedSpace

theorem norm_exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (x : A) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    ← sub_sub] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Exp

end GlobalTheory
