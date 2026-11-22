import Mathlib
import GroundTheory.GlobalFields.Artin.PlacesFrobenius
import GroundTheory.GlobalFields.Artin.PlacesInfinite
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

def fixedFieldMulEquiv : H ≃* Gal(L/fixedField H) where
  toFun := toFixedFieldAlgEquiv H
  invFun σ := ⟨σ.restrictScalars K, restrictScalars_mem H σ⟩
  left_inv _ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)
  right_inv _ := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl

omit [IsGalois K L] in
@[simp]
theorem fixedFieldMulEquiv_apply (h : H) (y : L) : fixedFieldMulEquiv H h y = (h : Gal(L/K)) y :=
  rfl

end GroundTheory.Global.Artin
