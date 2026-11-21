import Mathlib

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Inner

variable {G : Type*} [Group G] [Fintype G]

variable (G) in

def charInner : (G → ℂ) →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun χ ψ ↦ (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹)
    (fun χ χ' ψ ↦ by simp [add_mul, Finset.sum_add_distrib, mul_add])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)
    (fun χ ψ ψ' ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)

theorem charInner_apply (χ ψ : G → ℂ) :
    charInner G χ ψ = (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹ := rfl

def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

end Inner

section Characters

universe u

variable {G : Type*} [Group G] [Fintype G]

def IsIrrCharacter (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ

end Characters

end GroundTheory.LocalField
