import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)

omit [IsUltrametricDist K] in
private theorem Rl.neg {x y : K} (h : Rl x y) : Rl (-x) (-y) := by
  refine ⟨by simpa using h.1, ?_⟩
  rw [show -x - -y = -(x - y) by ring, norm_neg]
  exact h.2

private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

end Rel

end UpperTheory.V.Sd
