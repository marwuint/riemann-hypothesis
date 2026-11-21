import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace PluckerAffineCover

section Bundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

abbrev yyc : (Σ k, S.YIdx k) → S.Φ := T.yyCoord S.x S.δ S.e S.φ (S.a 0)

theorem yyc_base (i : S.ι) : yyc S ⟨.base, i⟩ = algebraMap S.Ω S.Φ (S.x i) := rfl

end Bundle

end PluckerAffineCover

end

end GroundTheory.Heights₂.Heights.Inter
