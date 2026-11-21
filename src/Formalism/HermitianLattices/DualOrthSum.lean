import Mathlib
import Formalism.HermitianLattices.StatementLat

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def DualOrthSum : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (V₁ V₂ : Submodule K V), IsCompl V₁ V₂ →
    (∀ x ∈ V₁, ∀ y ∈ V₂, h x y = 0) → (∀ x ∈ V₂, ∀ y ∈ V₁, h x y = 0) →
    ∀ L₁ L₂ : Submodule R V, (L₁ : Set V) ⊆ V₁ → (L₂ : Set V) ⊆ V₂ →
      dual h (L₁ ⊔ L₂) = (dual h L₁ ⊓ V₁.restrictScalars R) ⊔ (dual h L₂ ⊓ V₂.restrictScalars R)

end Formalism.HermitianLatticesTheory
