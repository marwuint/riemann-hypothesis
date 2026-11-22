import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DHPos : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    0 ≤ ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ)
        + iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I))).re

def DHCauchy : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ), 0 < r → 1 ≤ B →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ (k : ℕ) (s : ℂ), s ∈ Metric.closedBall z₀ (r / 12) → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ 72 * Real.log B / r * (12 / r) ^ k

def DHLocal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

def DHLocalOf : Prop := DHCauchy → DHLocal

end Formalism.HermitianLattices.Ext.PrimesInProgressions
