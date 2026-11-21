import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

def LiftO {O : Type*} [CommRing O] (ℓ : ℕ) {H₁ H₂ : Type*} [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ((ℓ : O) ^ e) • κ ∈ Hf₁.map g

def StatMono : Prop :=
  ∀ (O : Type*) [CommRing O] (ℓ : ℕ) (H₁ H₂ : Type*) [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e e' : ℕ), e ≤ e' → LiftO ℓ Hf₁ Hf₂ g e → LiftO ℓ Hf₁ Hf₂ g e'

end Formalism.RepresentationBoundsCohomology.JL
