import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LocalLat

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

abbrev mR (g : Matrix ι ι K) : (ι → K) →ₗ[R] (ι → K) := g.mulVecLin.restrictScalars R

theorem mR_apply (g : Matrix ι ι K) (x : ι → K) : mR (R := R) g x = g.mulVec x := rfl

variable (R) in

def chi (P : HeightOneSpectrum R) (g : Matrix ι ι K) : ℤ :=
  lidx P.asIdeal (std : Submodule R (ι → K)) ((std : Submodule R (ι → K)).map (mR g))

end PI.IsoDetW.Loc
