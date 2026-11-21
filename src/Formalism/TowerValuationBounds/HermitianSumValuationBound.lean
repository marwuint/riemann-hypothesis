import Mathlib

noncomputable section

namespace Formalism.ValuationGridEstimates

open Finset

def AbsValuationSumBound : Prop :=
  ∀ (W E : Type) [Fintype E] (lam val δ : W → ℝ) (absx : E → ℝ) (Wx : Finset W) (Bδ : ℝ),
    (∀ w, 0 ≤ lam w) → (∀ w, w ∉ Wx → val w = 0) →
    ∑ w ∈ Wx, lam w * val w = (∑ σ, Real.log (absx σ)) / Fintype.card E →
    (∑ w ∈ Wx, lam w * |val w| =
        (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    (∑ w ∈ Wx, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w)) ∧
    ((∀ w, 0 ≤ δ w) → (∀ w, -(3 * δ w) ≤ val w) → (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
      ∀ F : Finset W, ∑ w ∈ F, lam w * |val w| ≤
        (∑ σ, Real.posLog (absx σ)) / Fintype.card E + 6 * Bδ)

def PrimeLogSquareSumLtOne : Prop :=
  ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 < 1

def PrimeLogBudget : Prop :=
  ∀ (N0 : ℕ → ℝ) (BN0 : ℝ),
    (∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 l * Real.log l ≤ BN0) →
    ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l ≤ BN0 + 1

end Formalism.ValuationGridEstimates
