import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.SectionA

namespace ReciprocityTheory.Coh

open Function

universe u

theorem groupSection_holds : GroupSectionStatement.{u} := by
  intro G _ _ _ _ _ _ U hU
  obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
  let r0 : G → U := fun g => ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g)⟩
  have hr0 : Continuous r0 := (continuous_id.mul ht.inv).subtype_mk _
  refine ⟨fun g => r0 g * (r0 1)⁻¹, hr0.mul continuous_const, mul_inv_cancel _, ?_⟩
  intro x g
  have h : t (x * g) = t g := hc _ _ (by rw [mul_inv_cancel_right]; exact x.2)
  apply Subtype.ext
  simp only [r0, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]

end ReciprocityTheory.Coh
