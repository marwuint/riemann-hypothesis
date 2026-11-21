import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

namespace RationalModIntegerChains

open scoped Nat

variable {A : Type} [AddCommGroup A]

theorem qz_torsion (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨q.num, by
    show (q.num : ℚ) = _
    rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩

end RationalModIntegerChains

end ReciprocityTheory.DiscreteGroups.LocalClassField
