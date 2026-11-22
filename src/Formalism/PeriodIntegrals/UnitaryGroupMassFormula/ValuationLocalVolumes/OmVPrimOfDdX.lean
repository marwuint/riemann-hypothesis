import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVUnramHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.NegNatUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVSD_holds : OmVSD X := omVSD_of X (omVSDBwd_holds X)

theorem omVPrim_of_dd (hD : OmVDdLoc X) : OmVPrim X u' :=
  omVPrim_of X u' (omVMem_of X u' (omVMemEF_of X u' hD)) (omVZPrim_holds X u')

theorem omVSD_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVSD X := omVSD_holds X

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
