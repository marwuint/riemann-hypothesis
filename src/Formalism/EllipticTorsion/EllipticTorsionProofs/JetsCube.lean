import Mathlib
import Formalism.EllipticTorsion.JetsCube
import Formalism.FormalGroupLog.LogDeterminesLaw

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupCubeJets

open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

variable (F : FormalGroup (unitBall K))

theorem FK_eq : (FK F).toPowerSeries = MvPowerSeries.map (unitBall K).subtype F.toPowerSeries :=
  rfl

end Formalism.ELL.FormalGroupCubeJets

namespace Formalism.ELL

end Formalism.ELL
