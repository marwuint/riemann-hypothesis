import Formalism.GaussJetBounds.StatementI

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def JetsIntegral {K : Type u} [NormedField K] {ι : Type} (sg : MvPowerSeries ι K) : Prop :=
  ∀ κ : ι →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ sg‖ ≤ 1

end Formalism.DworkPowerSeriesWeights
