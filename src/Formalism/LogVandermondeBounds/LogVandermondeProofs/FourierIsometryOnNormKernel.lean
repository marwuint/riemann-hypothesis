import Formalism.LogVandermondeBounds.GaussOperatorProductFormula

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Helpers

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

private def smulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]

end Helpers

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
