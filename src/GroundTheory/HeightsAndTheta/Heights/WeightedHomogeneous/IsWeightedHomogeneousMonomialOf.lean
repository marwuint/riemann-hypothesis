import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace MonomialMap

theorem toFun_cast {P : ArithVariety n} {a b : ι → ℤ} (h : a = b) (s : IntegralSection P a) :
    (s.cast h).toFun = s.toFun := rfl

end MonomialMap

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
