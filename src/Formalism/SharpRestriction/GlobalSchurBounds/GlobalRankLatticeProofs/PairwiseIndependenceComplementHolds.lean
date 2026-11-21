import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

namespace BernoulliMarginals

end BernoulliMarginals

namespace UpperTriangularReduction

open Matrix Filter Topology Polynomial

section UT

variable {k : ℕ} {S : Type*} [CommRing S]

def UT (B : Matrix (Fin k) (Fin k) S) : Prop := B.BlockTriangular id ∧ ∀ i, B i i = 1

theorem diag_mul {A B : Matrix (Fin k) (Fin k) S} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem UT.mul {A B : Matrix (Fin k) (Fin k) S} (hA : UT A) (hB : UT B) : UT (A * B) :=
  ⟨hA.1.mul hB.1, fun i => by rw [diag_mul hA.1 hB.1, hA.2, hB.2, one_mul]⟩

end UT

variable (g k : ℕ) [Fact g.Prime]

end UpperTriangularReduction

end Formalism.MainNotions.UnusedSlot33

end
