import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K]

variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}

section Degrees

variable {R : Type*} [CommSemiring R]

end Degrees

variable {r : ℕ}

end LatticeModel

end

end GroundTheory.Heights₂.Heights
