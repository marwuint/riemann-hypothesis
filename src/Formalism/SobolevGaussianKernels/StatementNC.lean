import Mathlib

namespace Formalism.SL.NC

open Finset

def NormCharMean : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (ψ : AddChar K ℂ), (∃ c, ψ c ≠ 1) →
    ∀ (n : ℕ) (ℓ : Fin n → L), ℓ ≠ 0 →
      ‖∑ y ∈ univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = 0),
          ψ (∑ i, Algebra.trace K L (ℓ i * y i))‖
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

end Formalism.SL.NC
