import Mathlib

noncomputable section

namespace GroundTheory.Heights₂.Theta

open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise

section Field

variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]

def mulLeftAddEquiv (a : R) (ha : a ≠ 0) : R ≃ₜ+ R where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := inv_mul_cancel_left₀ ha x
  right_inv x := mul_inv_cancel_left₀ ha x
  map_add' x y := mul_add a x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem mulLeftAddEquiv_apply (a : R) (ha : a ≠ 0) (x : R) : mulLeftAddEquiv a ha x = a * x := rfl

variable [LocallyCompactSpace R] [T2Space R]

end Field

end GroundTheory.Heights₂.Theta
