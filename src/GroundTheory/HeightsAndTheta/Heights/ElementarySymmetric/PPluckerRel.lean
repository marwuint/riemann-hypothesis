import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace PluckerRelations

variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem coord_base (j : S.ι) :
    T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ⟨T.WBlk.base, j⟩ = algebraMap S.Ω S.Φ (S.x j) :=
  rfl

end PluckerRelations

end

end GroundTheory.Heights₂.Heights.Inter
