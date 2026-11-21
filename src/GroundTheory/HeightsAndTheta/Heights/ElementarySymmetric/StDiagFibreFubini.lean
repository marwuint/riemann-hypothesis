import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def diagWordMomentPoly (k i : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
      (pderiv 0 (pderiv 1 ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ))))

end

end GroundTheory.Heights₂.Heights.Inter
