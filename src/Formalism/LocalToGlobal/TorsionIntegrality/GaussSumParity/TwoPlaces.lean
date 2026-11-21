import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.GaussJetBounds.StatementW

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries

abbrev PV (ι : Type) (N0 N1 : ℕ) := Bool × ι × Fin N0 × Fin N1

end Formalism.L2.Th1.D
