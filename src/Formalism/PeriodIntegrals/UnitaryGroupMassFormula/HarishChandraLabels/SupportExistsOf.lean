import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
namespace PI.GreenHCLabel

def SimpleIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrrRep τ.ρ

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

variable {K}

end PI.GreenHCLabel
