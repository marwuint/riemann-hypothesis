import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

section Scale

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Scale

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
