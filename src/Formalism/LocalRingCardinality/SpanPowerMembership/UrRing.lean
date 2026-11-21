import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.Ur

open Polynomial IsLocalRing

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def ball (M : Subfield C) : Subring C where
  carrier := {x | x ∈ M ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, norm_one.le⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

variable (M : Subfield C)

theorem dvd_iff (a b : ball M) : a ∣ b ↔ ‖(b : C)‖ ≤ ‖(a : C)‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    by_cases ha : (a : C) = 0
    · have : b = 0 := Subtype.ext (by rw [ha, norm_zero] at h; exact norm_le_zero_iff.mp h)
      rw [this]; exact dvd_zero _
    · refine ⟨⟨b / a, div_mem b.2.1 a.2.1, ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · show (b : C) = a * (b / a)
        field_simp

theorem isUnit_iff (a : ball M) : IsUnit a ↔ ‖(a : C)‖ = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff, Subring.coe_one, norm_one]
  exact ⟨fun h => le_antisymm a.2.2 h, fun h => h.ge⟩

instance : IsLocalRing (ball M) := .of_nonunits_add fun a b ha hb => by
  rw [mem_nonunits_iff, isUnit_iff] at *
  exact ((IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt
    (max_lt (lt_of_le_of_ne a.2.2 ha) (lt_of_le_of_ne b.2.2 hb))).ne

def toM : ball M →+* M := (ball M).subtype.codRestrict M.toSubring fun x => x.2.1

instance : Algebra (ball M) M := (toM M).toAlgebra

instance : IsScalarTower (ball M) M C := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsFractionRing (ball M) M := by
  have hinj : Function.Injective (algebraMap (ball M) M) := fun a b h =>
    Subtype.ext (congrArg (fun t : M => (t : C)) h)
  have : FaithfulSMul (ball M) M := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖(z : C)‖ ≤ 1
  · exact ⟨⟨z, z.2, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · have h1 : ‖(z : C)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.mp h).le
    refine ⟨1, ⟨(z : C)⁻¹, inv_mem z.2, h1⟩, ?_⟩
    rw [map_one, one_div]
    exact Subtype.ext (inv_inv (z : C)).symm

def Disc (M : Subfield C) (π : C) : Prop := ∀ x ∈ M, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n

variable {M} {π : C} (hπ : π ∈ M) (h0 : π ≠ 0) (h1 : ‖π‖ < 1) (hD : Disc M π)

section Ext

variable (M) (ζ : C)

def ext : Subfield C := (IntermediateField.adjoin M {ζ}).toSubfield

theorem le_ext : M ≤ ext M ζ := fun y hy => (IntermediateField.adjoin M {ζ}).algebraMap_mem ⟨y, hy⟩

instance : Algebra (ball M) (ball (ext M ζ)) :=
  (Subring.inclusion (S := ball M) (T := ball (ext M ζ)) fun _ h => ⟨le_ext M ζ h.1, h.2⟩).toAlgebra

instance : IsScalarTower (ball M) (ball (ext M ζ)) C := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {M}

end Ext

end Formalism.BasicNotions.Examples₂.Ur
