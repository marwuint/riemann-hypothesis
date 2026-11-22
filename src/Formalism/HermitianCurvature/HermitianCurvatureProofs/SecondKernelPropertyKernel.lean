import Formalism.DoubleCosetMeasures.Statement

namespace Formalism.FourierDecayAlt.P.LastBlockReversal

theorem blk_last (l : List ℕ) : Formalism.DoubleCosetMeasures.blk (l ++ [1]) l.sum = l.length := by
  induction l with
  | nil => simp [Formalism.DoubleCosetMeasures.blk]
  | cons a l ih =>
    simp only [List.cons_append, List.sum_cons, List.length_cons, Formalism.DoubleCosetMeasures.blk]
    rw [if_neg (by omega), Nat.add_sub_cancel_left, ih]
    omega

end Formalism.FourierDecayAlt.P.LastBlockReversal

namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices

end Formalism.FourierDecayAlt.P.LastBlockReversalIndices

namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock

open Formalism.DoubleCosetMeasures

theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [revIn]
    split_ifs with hj
    · simp; omega
    · have := revIn_lt s (j - a) (by simp at h; omega)
      simp; omega

theorem revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, hj, if_true, h2]; omega
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, revIn_revIn s (j - a) (by simp at h; omega)]; omega

theorem blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    by_cases hj : j < a
    · have h2 : a - 1 - j < a := by omega
      simp only [revIn, blk, hj, if_true, h2]
    · have h2 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, blk, hj, if_false, h2]
      rw [Nat.add_sub_cancel_left, blk_revIn s (j - a) (by simp at h; omega)]

theorem pt_mul {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t * pt s (fun b => (t b)⁻¹) = (1 : Matrix (Fin s.sum) (Fin s.sum) K) := by
  ext a c
  simp only [Matrix.mul_apply, pt]
  rw [Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · rw [if_pos rfl]
    simp only [Fin.val_mk]
    rw [revIn_revIn s a a.2, blk_revIn s a a.2, Matrix.one_apply]
    by_cases h : c = a
    · subst h
      simp
    · have h' : (c : ℕ) ≠ a := fun e => h (Fin.ext e)
      simp [h', Ne.symm h]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro e
    exact hb (Fin.ext e)
  · simp

end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
