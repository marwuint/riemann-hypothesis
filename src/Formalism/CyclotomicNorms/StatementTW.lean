import Mathlib

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖

abbrev TruncK (K' : Type) [Field K'] (n : ℕ) : Type := K'[X] ⧸ Ideal.span {(X : K'[X]) ^ n}

end Formalism.CyclotomicNorms
