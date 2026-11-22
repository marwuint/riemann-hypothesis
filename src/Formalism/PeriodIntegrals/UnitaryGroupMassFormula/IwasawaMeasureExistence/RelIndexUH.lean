import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd

noncomputable section

namespace PI.IwaMeasEx.MFI

open NumberField
open scoped TensorProduct nonZeroDivisors Pointwise
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

variable (I : AutInst)

def oH : AddSubgroup (AEf I) := (IntAf I.F I.E).toAddSubgroup

def uH (u : AEf I) : AddSubgroup (AEf I) := (oH I).map (AddMonoidHom.mulLeft u)

def aI (u : (AEf I)ˣ) : Ideal (𝓞 I.E) := Submodule.comap (Algebra.linearMap (𝓞 I.E) I.E) (cid I u)

end PI.IwaMeasEx.MFI

end
