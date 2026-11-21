import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagComplexPointsOverX

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Matrix Equiv

namespace FdegNeZero

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : Fin N :=
  ⟨if (i : ℕ) < j then j - 1 - i else N - 1 + j - i, by split_ifs <;> omega⟩

theorem rev_rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : rev j hj (rev j hj i) = i := by
  apply Fin.ext
  simp only [rev]
  split_ifs <;> omega

def rho (j : ℕ) (hj : j ≤ N) : Perm (Ψ × Fin N) :=
  Function.Involutive.toPerm (fun x => (x.1, rev j hj x.2)) fun x => by simp [rev_rev]

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rho_apply (j : ℕ) (hj : j ≤ N) (x : Ψ × Fin N) : rho j hj x = (x.1, rev j hj x.2) := rfl

end FdegNeZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
