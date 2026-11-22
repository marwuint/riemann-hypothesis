import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.SpanSingletonAlgebraMap

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

def std : Submodule R (ι → K) := Submodule.pi Set.univ (fun _ => (1 : Submodule R K))

def sc (a : K) : Submodule R (ι → K) :=
  Submodule.pi Set.univ (fun _ => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) a : FI) : Submodule R K))

end PI.IsoDetW.Loc
