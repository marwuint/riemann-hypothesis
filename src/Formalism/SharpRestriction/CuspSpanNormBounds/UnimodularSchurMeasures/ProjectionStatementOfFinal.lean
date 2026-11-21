import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuCountOfPack

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.LocGrowth (X : CData) : Prop :=
  ∀ (v : InfinitePlace X.I.F) (s : ℝ), 0 ≤ s →
    (1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g : Formalism.REAL.UJ (X.I.ε v) =>
      ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g)) (Formalism.REAL.muG (X.I.ε v))

end Formalism.MainNotions.LeviCoordinates
