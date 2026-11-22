import Formalism.EllipticTorsion.Statement
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

noncomputable section

open PowerSeries

universe u

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

section Ring

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => MvPowerSeries.subst (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries

end Ring

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL.PadicMultiplication

end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL

end Formalism.ELL
