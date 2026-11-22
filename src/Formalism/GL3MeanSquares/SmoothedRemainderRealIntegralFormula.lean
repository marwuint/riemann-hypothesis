import Mathlib
import Formalism.LandauZeroFreeBounds.Statement

open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2PrimeSums

def psum (a : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def psumR (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def Gchi (a : ℕ → ℂ) (S : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) - (y : ℂ) * S

def Gone (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def SmoothedRemainderIntegralFormula : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℂ,
      Tendsto (fun U : ℝ => ∫ u in y..U, psum a u / (u : ℂ) ^ 2) atTop (𝓝 I) ∧
      Gchi a S y = -(y : ℂ) * I

def SmoothedRemainderRealIntegralFormula : Prop :=
  ∀ a : ℕ → ℝ,
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR a u - u) / u ^ 2) atTop
      (𝓝 (-1 - Real.eulerMascheroniConstant)) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℝ,
      Tendsto (fun U : ℝ => ∫ u in y..U, (psumR a u - u) / u ^ 2) atTop (𝓝 I) ∧
      Gone a y = -y * I

def GoodFor (Q : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → ¬ Formalism.ZeroFreeDirichlet.IsLZero χ s

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def Emain (θ : ℤ) (β X : ℝ) : ℝ := Li X - θ * Li (X ^ β)

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-c * Real.log X / Real.log B) + C * Real.exp (-c * Real.sqrt (Real.log X))

def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X

def PrimesAPInterval (C₀ Cr cr c : ℝ) : Prop :=
  ∀ (m a : ℕ), 3 ≤ m → Nat.Coprime a m → ∀ Y h : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y → h ≤ 1 →
    rhoErr Cr cr (4 * m) Y ≤ h / 100 → (4 * (m : ℝ)) ^ (7 : ℝ) ≤ h * Y ^ ((1 : ℝ) / 3) →
    c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ)

def PP (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Ioc ⌊Real.sqrt X⌋₊ ⌊X⌋₊).filter (fun q => q.Prime ∧ q ≡ a₀ [MOD m₀])

end Formalism.HermitianLattices.GL2PrimeSums
