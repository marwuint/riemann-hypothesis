import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def CSize.PackCount {X : CData} (S : CSize X) : Prop :=
  ∀ x : X.I.GA, ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ T : Finset X.I.GFset,
    (∀ γ ∈ T, X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 ∧ ∀ v, X.dist x γ v ≤ r v) →
    (T.card : ℝ) ≤
      (1 + 2 * (∏ v, Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) /
        S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F))

end Formalism.MainNotions.LeviCoordinates

end
