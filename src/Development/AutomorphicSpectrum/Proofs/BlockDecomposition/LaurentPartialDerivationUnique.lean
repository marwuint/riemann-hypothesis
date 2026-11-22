import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.ConeRes

open AddMonoidAlgebra

variable {K : Type} [Field K] {d : ℕ}

noncomputable def logDer (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ))
    (AddMonoidAlgebra K (Fin d →₀ ℤ))) :
    (Fin d →₀ ℤ) →+ AddMonoidAlgebra K (Fin d →₀ ℤ) where
  toFun m := single (-m) 1 * D (single m 1)
  map_zero' := by
    have h : (single (0 : Fin d →₀ ℤ) (1 : K)) = 1 := one_def.symm
    rw [h, D.map_one_eq_zero, mul_zero]
  map_add' m n := by
    have h : (single (m + n) (1 : K)) = single m 1 * single n 1 := by
      rw [single_mul_single, one_mul]
    have hm : (single (-m) (1 : K)) * single m 1 = 1 := by
      rw [single_mul_single, one_mul, neg_add_cancel, one_def]
    have hn : (single (-n) (1 : K)) * single n 1 = 1 := by
      rw [single_mul_single, one_mul, neg_add_cancel, one_def]
    have hs : (single (-(m + n)) (1 : K)) = single (-m) 1 * single (-n) 1 := by
      rw [single_mul_single, one_mul, neg_add]
    rw [h, D.leibniz, hs]
    simp only [smul_eq_mul]
    linear_combination (single (-n) (1 : K) * D (single n 1)) * hm +
      (single (-m) (1 : K) * D (single m 1)) * hn

end GlobalTheory.CompanionTheory.ConeRes
