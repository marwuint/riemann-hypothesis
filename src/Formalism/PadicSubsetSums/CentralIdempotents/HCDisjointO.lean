import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

section Reps

variable {Γ : Type} [Group Γ]

def RepIso {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ γ v, e (ρ γ v) = ρ' γ (e v)

end Reps

end Formalism.IrreducibleCountingLemmas.TYPES
