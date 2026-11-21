import Mathlib
import GroundTheory.GlobalFields.Artin.PlacesGalois
import GroundTheory.GlobalFields.Artin.Series
import GroundTheory.GlobalFields.Artin.InflationTower

set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField GroundTheory.LocalField

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

def fixedFieldFun (f : H → ℂ) : Gal(L/fixedField H) → ℂ :=
  f ∘ (fixedFieldMulEquiv H).symm

omit [IsGalois K L] in
@[simp]
theorem fixedFieldFun_apply (f : H → ℂ) (h : H) :
    fixedFieldFun H f (fixedFieldMulEquiv H h) = f h := by
  simp [fixedFieldFun]

end GroundTheory.Global.Artin
