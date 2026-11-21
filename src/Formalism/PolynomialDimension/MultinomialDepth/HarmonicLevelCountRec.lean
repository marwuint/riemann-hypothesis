import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)

theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B

end Formalism.CountingSumsFrames
