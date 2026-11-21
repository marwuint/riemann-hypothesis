import Formalism.LogFactorialBounds.LocalFactorSplit

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

def LocalFactorTameDv : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (r t j : ℕ), 1 ≤ j → ∀ L : ℝ,
    (q ^ (r * j * t) * qE q 1 (r + j * t) / (qE q 1 r * qE q 1 (j * t))) *
        (qE q (t + 1) (r + j * t))⁻¹ *
        (q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r * L / (qE q (t + 1) (j * t))⁻¹) =
      L

def laguerre (n α : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * ((n + α).choose (n - k) : ℝ) * x ^ k / (k.factorial : ℝ)

def LaguerreCoeffBound : Prop :=
  ∀ (i j D : ℕ), i ≤ j → j ≤ D → ∀ s : ℝ, 0 ≤ s →
    Real.exp (-(s ^ 2) / 2) * Real.sqrt ((i.factorial : ℝ) / (j.factorial : ℝ)) * s ^ (j - i) *
        |laguerre i (j - i) (s ^ 2)| ≤
      Real.exp (-(s ^ 2) / 2) * (2 * (1 + s ^ 2)) ^ D

def ExpPowAbsorb : Prop :=
  ∀ R P : ℝ, 0 < R → 0 < P →
    Real.exp (-(π * R)) * R ^ P ≤ Real.exp (-((π - 1) * R)) * P ^ P

def PrimeSetLogSum : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
    ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ 10 * Real.log B

end Formalism.LogFactorialBounds
