import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open scoped TensorProduct nonZeroDivisors

section Kap

variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]

theorem isFrac_tensor (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A) := inferInstance
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  · intro r hr
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := A) (I := Ideal.span {r}) hr0
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)
    have hu : IsUnit (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B d)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) _
        ⟨_, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0, rfl⟩⟩
    rw [hs, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu

def kap (hinj : Function.Injective (algebraMap A B)) : (B ⊗[A] FractionRing A) ≃ₐ[B] FractionRing B :=
  haveI := isFrac_tensor A B hinj
  IsLocalization.algEquiv B⁰ _ _

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def vecE (hinj : Function.Injective (algebraMap A B)) :
    (ι → FractionRing B) ≃ₗ[B] B ⊗[A] (ι → FractionRing A) :=
  (LinearEquiv.piCongrRight fun _ : ι => (kap A B hinj).symm.toLinearEquiv) ≪≫ₗ
    (TensorProduct.piRight A B B (fun _ : ι => FractionRing A)).symm

end Kap

end Formalism.BasicNotions.Examples₂.NZ
