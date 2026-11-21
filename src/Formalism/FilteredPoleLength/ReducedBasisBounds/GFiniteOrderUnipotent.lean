import Mathlib

open scoped BigOperators
open Polynomial Finset

namespace Formalism.LatticeBaseChangeAlt

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

end Formalism.LatticeBaseChangeAlt
