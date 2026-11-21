import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D)

def tau : 𝓞 X.B.I.E →+* 𝓞 X.B.I.E := RingOfIntegers.mapRingHom (starRingEnd X.B.I.E)

theorem tau_coe (x : 𝓞 X.B.I.E) :
    algebraMap (𝓞 X.B.I.E) X.B.I.E (tau X x) = star (algebraMap (𝓞 X.B.I.E) X.B.I.E x) := rfl

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
