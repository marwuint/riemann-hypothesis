import Mathlib

namespace GlobalTheory.CMNorm

open Matrix

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

def lam {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) : R →ₗ[A] A where
  toFun r := e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1)
  map_add' x y := by simp [add_smul]
  map_smul' a x := by simp [smul_assoc]

theorem lam_apply {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (r : R) : lam e₁ f₁ r = e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1) := rfl

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

end GlobalTheory.CMNorm
