import Mathlib

open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements

def AutCount : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ) (v : Fin e → M),
    Submodule.span R (Set.range v) = ⊤ → Nat.card (M ≃ₗ[R] M) ≤ Nat.card M ^ e

end Formalism.SLP.GlobalBoundRefinements
