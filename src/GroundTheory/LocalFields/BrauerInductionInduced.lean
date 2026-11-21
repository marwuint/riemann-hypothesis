import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section IndFun

variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]

open Classical in

def indFun (φ : H →* G) : (H → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun ψ s := (Nat.card H : ℂ)⁻¹ * ∑ t : G, ∑ h : H, if φ h = t⁻¹ * s * t then ψ h else 0
  map_add' ψ ψ' := by
    funext s
    simp only [Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    split_ifs <;> simp
  map_smul' c ψ := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_left_comm c]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    split_ifs <;> simp

open Classical in
theorem indFun_apply (φ : H →* G) (ψ : H → ℂ) (s : G) :
    indFun φ ψ s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, ∑ h : H, if φ h = t⁻¹ * s * t then ψ h else 0 := rfl

omit [Fintype G] [Fintype H] in

theorem IsClassFun.comp {χ : G → ℂ} (hχ : IsClassFun χ) (φ : H →* G) : IsClassFun (χ ∘ φ) := by
  intro h k
  simp only [Function.comp_apply, map_mul, map_inv]
  exact hχ _ _

end IndFun

end GroundTheory.LocalField
