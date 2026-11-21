import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LidxAntisymm

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

theorem coe_le_one {I : FI} (h : I ≤ 1) : (I : Submodule R K) ≤ 1 :=
  (FractionalIdeal.coe_le_coe.mpr h).trans_eq FractionalIdeal.coe_one

end PI.IsoDetW.Loc
