import Mathlib

namespace Formalism.FourierDecayAlt

open Finset Real NumberField

def RecursionText : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1/2 → 0 ≤ ε → ε ≤ a → (r : ℝ) * a ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * a) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt
