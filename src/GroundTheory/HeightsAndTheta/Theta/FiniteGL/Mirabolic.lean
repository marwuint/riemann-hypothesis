import Mathlib

namespace GroundTheory.Heights₂.Theta

namespace FinGL

open Matrix

noncomputable section

section Flags

variable (n : ℕ) (F : Type*) [Field F]

structure Flag where

  length : ℕ

  space : Fin (length + 1) → Submodule F (Fin n → F)
  mono : Monotone space
  space_zero : space 0 = ⊥
  space_last : space (Fin.last length) = ⊤

variable {n F}

end Flags

end

end FinGL

end GroundTheory.Heights₂.Theta
