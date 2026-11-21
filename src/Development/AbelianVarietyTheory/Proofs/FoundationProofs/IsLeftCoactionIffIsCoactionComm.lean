import Mathlib

open TensorProduct Coalgebra

namespace GlobalTheory

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

structure IsCoaction (ρ : M →ₗ[R] M ⊗[R] C) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R M C C (ρ.rTensor C (ρ m)) =
    (comul : C →ₗ[R] C ⊗[R] C).lTensor M (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).lTensor M (ρ m) = m ⊗ₜ[R] (1 : R)

theorem IsCoaction.rid_counit {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) (m : M) :
    TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M (ρ m)) = m := by
  simp [h.counit]

theorem IsCoaction.injective {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) : Function.Injective ρ :=
  Function.LeftInverse.injective
    (g := fun t => TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M t))
    h.rid_counit

def coactionWeightSpace (ρ : M →ₗ[R] M ⊗[R] C) (g : C) : Submodule R M :=
  LinearMap.eqLocus ρ ((TensorProduct.mk R M C).flip g)

omit [Coalgebra R C] in
@[simp] theorem mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M} :
    m ∈ coactionWeightSpace ρ g ↔ ρ m = m ⊗ₜ[R] g := Iff.rfl

end GlobalTheory
