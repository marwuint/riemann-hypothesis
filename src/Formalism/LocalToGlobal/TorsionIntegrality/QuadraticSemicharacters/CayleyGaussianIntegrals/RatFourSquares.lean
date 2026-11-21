import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.InterIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def PD {n : Type*} [Fintype n] (h : Matrix n n ℂ) : Prop :=
  ∀ x : n → ℂ, x ≠ 0 → 0 < (∑ i, ∑ j, x i * h i j * conj (x j)).re

end Formalism.L2.Th1.H
