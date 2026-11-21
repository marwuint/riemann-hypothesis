import Formalism.GaussJetBounds.StatementN

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def IntOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type) (Th : MvPowerSeries ι K),
    JetsIntegral Th → ∀ P : MvPolynomial ι K, (∀ n, ‖MvPolynomial.coeff n P‖ ≤ 1) →
      ‖jetPair P Th‖ ≤ 1

end Formalism.DworkPowerSeriesWeights
