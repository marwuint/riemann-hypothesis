import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor

def dets (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ L) ∧ d = (Matrix.of y).det}

end GlobalTheory.IdxTensor

end
