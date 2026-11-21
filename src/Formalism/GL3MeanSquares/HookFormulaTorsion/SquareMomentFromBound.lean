import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem column_top_entry : LastColumnBound := by
  intro κ lam A bt S hbt hS h0 hl hmid
  have hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S := by
    intro j
    by_cases hj : j.succ = Fin.last (κ + 1)
    · rw [hj, hl]; linarith
    · exact (hmid j.succ (Fin.succ_ne_zero j) hj).2
  have hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S := by
    calc ∑ j : Fin (κ + 1), lam j.succ ≤ ∑ _j : Fin (κ + 1), S := Finset.sum_le_sum fun j _ => hsucc j
      _ = (κ + 1) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  constructor
  · unfold wt
    rw [Fin.sum_univ_succ, h0]
    nlinarith
  · unfold wt plus
    rw [Fin.sum_univ_succ, h0, hl]
    have e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    nlinarith

end Formalism.HermitianLattices.TraceIntegrality
