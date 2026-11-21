import Mathlib

open Finset

noncomputable section

namespace Formalism.HadamardInequality

def GlRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

end Formalism.HadamardInequality
