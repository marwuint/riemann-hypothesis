import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LandherrCSA

noncomputable section
namespace GlobalTheory.UStab
open GlobalTheory.HermCSA
open scoped TensorProduct

abbrev sK {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K] : K ⊗[ℤ] C →+ K ⊗[ℤ] C :=
  (ext C K s).toAddMonoidHom

section Ext
variable {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K]

@[simp] theorem sK_tmul (k : K) (c : C) : sK s K (k ⊗ₜ c) = k ⊗ₜ s c := rfl

end Ext

section Alg
variable {R : Type} [Ring R] (σ : R →+ R)

theorem σ_one (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) : σ 1 = 1 := by
  have h := hm (σ 1) 1
  rw [mul_one, hi] at h
  simpa using h.symm

def σU (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) : Rˣ :=
  ⟨σ u, σ ↑u⁻¹, by rw [← hm, Units.inv_mul, σ_one σ hm hi], by rw [← hm, Units.mul_inv, σ_one σ hm hi]⟩

end Alg

end GlobalTheory.UStab

namespace GlobalTheory.UStab
open GlobalTheory.HermCSA NumberField
open scoped TensorProduct

section Loc
variable {C : Type} [Ring C] (s : C →+ C) (hm : ∀ x y, s (x * y) = s y * s x) (hi : ∀ x, s (s x) = x)
  (K : Type) [CommRing K]

def uK (x : Cˣ) : (K ⊗[ℤ] C)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] K ⊗[ℤ] C).toMonoidHom x

include hm hi

end Loc
end GlobalTheory.UStab

namespace GlobalTheory.UStab
end GlobalTheory.UStab
