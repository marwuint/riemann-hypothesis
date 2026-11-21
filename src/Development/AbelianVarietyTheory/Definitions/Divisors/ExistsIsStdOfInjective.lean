import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers TensorProduct

namespace GlobalTheory.PDA.Model

variable {B : Type} [CommRing B] {J : Ideal B}

def gam (n : ℕ) (x : ZMod 4) : ZMod 4 :=
  if x = 0 ∨ x = 2 then (if n = 0 then 1 else if n = 1 ∨ n = 4 then x else 0) else 0

end GlobalTheory.PDA.Model
