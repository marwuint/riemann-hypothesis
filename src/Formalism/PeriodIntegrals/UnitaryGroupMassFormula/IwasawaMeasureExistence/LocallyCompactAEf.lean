import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.RelIndexUH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviSizesMeasurable

noncomputable section

attribute [to_additive measure_eq_addRelIndex_mul] PI.IwaMeasEx.MF.measure_eq_relIndex_mul
attribute [to_additive addHaar_map_eq_addRelIndex] PI.IwaMeasEx.MF.haar_map_eq_relIndex

namespace PI.IwaMeasEx.MFI

open MeasureTheory Measure NumberField
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

section

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf

theorem locallyCompact_AEf : LocallyCompactSpace (AEf I) :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact_IntAf I)
    ((isOpen_IntAf I).mem_nhds (zero_mem _))

attribute [local instance] locallyCompact_AEf

def mulU (u : (AEf I)ˣ) : AEf I ≃ₜ+ AEf I where
  toFun x := (u : AEf I) * x
  invFun x := ((u⁻¹ : (AEf I)ˣ) : AEf I) * x
  left_inv x := by simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

end

end PI.IwaMeasEx.MFI

end
