import Mathlib

open Finset

noncomputable section

namespace PI.RamBoundW

section Fil

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*} (δ : ι → Derivation R P P)

def apL : List ι → P →ₗ[R] P
  | [] => LinearMap.id
  | i :: T => apL T ∘ₗ (δ i).toLinearMap

@[simp] theorem apL_nil (M : P) : apL δ [] M = M := rfl

@[simp] theorem apL_cons (i : ι) (T : List ι) (M : P) : apL δ (i :: T) M = apL δ T (δ i M) := rfl

variable {δ}

end Fil

end PI.RamBoundW
