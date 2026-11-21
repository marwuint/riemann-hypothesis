import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace RigSymForm

variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)

abbrev Fn : Type := (Fin P.g → ℂ) → ℂ

end RigSymForm

open RigSymForm

end

end GroundTheory.Heights₂.Heights.KeyFormula
