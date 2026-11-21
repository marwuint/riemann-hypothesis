import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ThetaSummability.Real

section Defs

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsCCR {X : Type*} [DecidableEq X] (α β : X → Module.End ℂ M) : Prop where
  β_α : ∀ x y, β x * α y - α y * β x = if x = y then 1 else 0
  α_α : ∀ x y, α x * α y = α y * α x
  β_β : ∀ x y, β x * β y = β y * β x

variable {n N : ℕ}

end Defs

def sgn {m : ℕ} (ε : Fin m → Bool) (a : Fin m) : ℂ := if ε a then 1 else -1

end ReciprocityTheory.ThetaSummability.Real
