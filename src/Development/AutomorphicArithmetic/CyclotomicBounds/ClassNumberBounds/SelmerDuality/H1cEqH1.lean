import Mathlib

namespace KStar.Selmer

open Matrix Module

section Complex

variable {R : Type*} [CommRing R] {m n m' n' : Type*}

def coefMap [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    (n → M) →ₗ[R] (m → M) :=
  LinearMap.pi fun i => ∑ j, Φ i j • LinearMap.proj j

theorem coefMap_apply [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M]
    (v : n → M) (i : m) : coefMap Φ M v i = ∑ j, Φ i j • v j := by
  simp [coefMap, LinearMap.sum_apply]

def H1c [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R (n → M) :=
  LinearMap.ker (coefMap Φ M)

abbrev H2 [Fintype n] (Φ : Matrix m n R) : Type _ :=
  (m → R) ⧸ LinearMap.range Φ.mulVecLin

structure IsQis [Fintype m] [Fintype n] [Fintype n'] (Φ : Matrix m n R) (Φ' : Matrix m' n' R)
    (f₁ : Matrix n' n R) (f₂ : Matrix m' m R) : Prop where
  comm : Φ' * f₁ = f₂ * Φ
  inj₁ : ∀ x, Φ *ᵥ x = 0 → f₁ *ᵥ x = 0 → x = 0
  surj₁ : ∀ x', Φ' *ᵥ x' = 0 → ∃ x, Φ *ᵥ x = 0 ∧ f₁ *ᵥ x = x'
  inj₂ : ∀ y x', f₂ *ᵥ y = Φ' *ᵥ x' → ∃ x, y = Φ *ᵥ x
  surj₂ : ∀ y', ∃ y x', y' = f₂ *ᵥ y + Φ' *ᵥ x'

structure SelfDual [Fintype m] [Fintype n] (ε : R) (Φ : Matrix m n R) where

  J₁₂ : Matrix n m R

  J₂₁ : Matrix m n R

  H : Matrix m m R
  qis : IsQis Φ Φᵀ J₂₁ J₁₂
  symm : J₁₂ - ε • J₂₁ᵀ = Φᵀ * H

end Complex

section Special

variable {Λ O : Type*} [CommRing Λ] [CommRing O] {m n : Type*}

abbrev FracMod (O K : Type*) [CommRing O] [Field K] [Algebra O K] : Type _ :=
  K ⧸ (1 : Submodule O K)

end Special

end KStar.Selmer
