import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

namespace BlockSurjectivity

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def coeffVec (M : Finset (Coord n →₀ ℕ)) : MvPolynomial (Coord n) ℂ →ₗ[ℂ] (M → ℂ) :=
  LinearMap.pi fun μ ↦ lcoeff ℂ μ.1

omit [Fintype ι] [DecidableEq ι] in
theorem coeffVec_apply (M : Finset (Coord n →₀ ℕ)) (g : MvPolynomial (Coord n) ℂ) (μ : M) :
    coeffVec M g μ = coeff μ.1 g := rfl

end BlockSurjectivity

end

end GroundTheory.Heights₂.Heights
