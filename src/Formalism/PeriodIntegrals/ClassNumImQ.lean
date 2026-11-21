import Mathlib

open NumberField

namespace PI.ClassNumImQ

def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤

def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)

end PI.ClassNumImQ
