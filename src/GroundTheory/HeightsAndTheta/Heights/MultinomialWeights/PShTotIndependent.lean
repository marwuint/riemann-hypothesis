import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

variable (d : IndexData)

theorem shOn_apply (τ : Fin d.f) (F : topSpace d) : shOn d τ F = shiftFl d τ F := rfl

theorem totOn_apply (τ : Fin d.f) (F : topSpace d) : totOn d τ F = totalFl d τ F := rfl

end GroundTheory.Heights₂.Heights.TheoremB
