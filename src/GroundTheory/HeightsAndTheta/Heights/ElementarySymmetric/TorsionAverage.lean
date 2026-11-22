import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ZeroSetFinite
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace RigSymForm

variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)

def latVec (u v : Fin P.g → ℤ) : Fin P.g → ℂ := intVec v + P.pt.τ *ᵥ intVec u

def autL (N : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : ℂ :=
  perFactor P.ch N v * autFactor P.pt P.ch N u w

end RigSymForm

open RigSymForm

end

end GroundTheory.Heights₂.Heights.KeyFormula
