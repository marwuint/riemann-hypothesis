import Mathlib

noncomputable section

namespace Formalism.ResultantValuation

def LTEUnit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ i : ℕ, 1 ≤ i → ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i

end Formalism.ResultantValuation
