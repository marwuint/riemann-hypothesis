import Mathlib

noncomputable section

namespace GlobalTheory.SSG

def stdStep {C : Type} [CommRing C] (ϖ : C) {n : ℕ} (i : Fin n) : (Fin n → C) →ₗ[C] (Fin n → C) where
  toFun v j := if j = i then ϖ * v j else v j
  map_add' v w := by
    funext j
    by_cases h : j = i <;> simp [h, mul_add]
  map_smul' c v := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul, mul_left_comm]

structure LMPoint (C : Type) [CommRing C] (ϖ : C) (n : ℕ) [NeZero n] where

  ℓ : Fin n → Submodule C (Fin n → C)

  line : ∀ i, ∃ v : Fin n → C, ℓ i = Submodule.span C {v} ∧ Ideal.span (Set.range v) = ⊤

  step : ∀ i, (ℓ i).map (stdStep ϖ i) ≤ ℓ (i + 1)

end GlobalTheory.SSG

end
