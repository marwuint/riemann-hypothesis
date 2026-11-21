import Mathlib

open Polynomial

noncomputable section

namespace Formalism.D.Classical

section
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def grUnipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

end

variable {g : ℕ} [Fact g.Prime]

end Formalism.D.Classical

namespace Formalism.D.Classical

end Formalism.D.Classical
