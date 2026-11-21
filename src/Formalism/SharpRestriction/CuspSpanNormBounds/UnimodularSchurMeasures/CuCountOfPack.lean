import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def CSize.Inv {X : CData} (S : CSize X) : Prop := ∀ γ ∈ X.I.GFset, ∀ y, S.tau1 (γ * y) = S.tau1 y

def CSize.Lip {X : CData} (S : CSize X) : Prop :=
  ∀ y g, X.φ g ≠ 0 →
    S.tau1 y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ S.tau1 (y * g)

def CSize.LowN {X : CData} (S : CSize X) : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ S.tau1 (m * x)

end Formalism.MainNotions.LeviCoordinates
