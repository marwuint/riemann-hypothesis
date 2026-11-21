import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

def CountRhoArithStatement : Prop :=
  ∀ (n T δ dV ρ : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T →
    δ * (T - 1).choose n + ρ ≤ dV → dV ≤ δ * (T + 2 * n + 6).choose n →
    (ρ : ℝ) ≤ 22 * (n : ℝ) ^ 2 * dV / T

end ReciprocityTheory.ChartRestriction.G.AR.Up
