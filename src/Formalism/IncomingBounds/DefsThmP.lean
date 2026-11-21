import Formalism.IncomingBounds.StatementThmP
import Formalism.IncomingBounds.LevelTail
import Formalism.IncomingBounds.LemmaMNumerics

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

variable {C : Type} [Field C]

def ExpAdd : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (σ : Type) (a b : MvPowerSeries σ C),
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      mvExp (a + b) = mvExp a * mvExp b

end Formalism.IncomingBounds
