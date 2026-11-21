import Mathlib
import Formalism.GL3MeanSquares.SignsFromTrianglesSquares

noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation.PadicSquareSumIntegrality

open Finset

def allEmbeddingsUnitCircle : Subgroup ℂˣ where
  carrier := {w | ∀ s : ℂ →+* ℂ, ‖s (w : ℂ)‖ = 1}
  one_mem' := by intro s; simp
  mul_mem' := by
    intro a b ha hb s
    simp only [Units.val_mul, map_mul, norm_mul, ha s, hb s, mul_one]
  inv_mem' := by
    intro a ha s
    simp only [Units.val_inv_eq_inv_val, map_inv₀, norm_inv, ha s, inv_one]

theorem exists_pow_eq_unit_circle (w : allEmbeddingsUnitCircle) (n : ℕ) (hn : n ≠ 0) : ∃ b : allEmbeddingsUnitCircle, b ^ n = w := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq ((w : ℂˣ) : ℂ) (Nat.pos_of_ne_zero hn)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hβ
    exact (Units.ne_zero (w : ℂˣ)) hβ.symm
  refine ⟨⟨Units.mk0 β hβ0, ?_⟩, ?_⟩
  · intro s
    have h1 : ‖s ((w : ℂˣ) : ℂ)‖ = 1 := w.2 s
    rw [← hβ, map_pow, norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1
  · apply Subtype.ext; apply Units.ext
    simp [hβ]

instance unitCircleDivisibleNat : DivisibleBy (Additive allEmbeddingsUnitCircle) ℕ where
  div a n := if h : n = 0 then 0 else Additive.ofMul (Classical.choose (exists_pow_eq_unit_circle a.toMul n h))
  div_zero a := by simp
  div_cancel {n} a hn := by
    simp only [hn, dite_false]
    have := Classical.choose_spec (exists_pow_eq_unit_circle a.toMul n hn)
    change Additive.ofMul ((Classical.choose (exists_pow_eq_unit_circle a.toMul n hn)) ^ n) = a
    rw [this]; rfl

instance unitCircleDivisibleInt : DivisibleBy (Additive allEmbeddingsUnitCircle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _

end Formalism.HermitianLattices.WeilRepresentation.PadicSquareSumIntegrality
