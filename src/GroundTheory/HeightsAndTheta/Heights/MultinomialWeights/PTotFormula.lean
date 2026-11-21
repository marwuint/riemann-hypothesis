import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem intFl_apply (d : IndexData) (G : XPoly d) :
    intFl d G = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N G := rfl

end GroundTheory.Heights₂.Heights.TheoremB
