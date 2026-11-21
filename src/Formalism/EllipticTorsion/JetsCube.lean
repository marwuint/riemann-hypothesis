import Mathlib
import Formalism.EllipticTorsion.Statement

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

abbrev FK (F : FormalGroup (unitBall K)) : FormalGroup K := F.map (unitBall K).subtype

def omegaF (F : FormalGroup (unitBall K)) : PowerSeries K :=
  MvPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries K)]
    (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)

abbrev Y3 (i : Fin 3) : MvPowerSeries (Fin 3) K := MvPowerSeries.X i

def F2 (F : FormalGroup (unitBall K)) (i j : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![Y3 i, Y3 j] (FK F).toPowerSeries

end Formalism.ELL
