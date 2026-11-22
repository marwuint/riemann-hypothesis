import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def wwLinProd (k : ℕ) (u : ℕ → Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∏ n ∈ Finset.range (2 * k), (C (u n 0) * X 0 + C (u n 1) * X 1)

def wwLogWeight (p : S2 × S2) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2)

end

end GroundTheory.Heights₂.Heights.Inter
