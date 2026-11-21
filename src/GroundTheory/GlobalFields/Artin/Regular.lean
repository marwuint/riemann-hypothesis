import Mathlib
import GroundTheory.GlobalFields.Artin.InductionLocal
import GroundTheory.GlobalFields.Artin.Series

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain IntermediateField GroundTheory.LocalField

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [IsGalois K L] in

theorem fixedFieldFun_one (H : Subgroup Gal(L/K)) : fixedFieldFun H (1 : H → ℂ) = 1 := rfl

end GroundTheory.Global.Artin
