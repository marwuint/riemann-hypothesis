import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic

open Complex GlobalTheory.Glob.IntegralWittCoefficients

def IsPeriodLattice (Λ : AddSubgroup ℂ) (ω₁ τ : ℂ) : Prop :=
  ∀ x : ℂ, x ∈ Λ ↔ ∃ m n : ℤ, x = ω₁ * ((m : ℂ) + (n : ℂ) * τ)

def thetaChar (a b : Fin 2) (z τ : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
      (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (z + ((b : ℕ) : ℂ) / 2)) *
    jacobiTheta₂ (z + (((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ

def IsEvenChar (a b : Fin 2) : Prop := (a : ℕ) * (b : ℕ) = 0

def NormTheta0 : Prop :=
  ∀ (Λ : AddSubgroup ℂ) (ω₁ τ t₀ : ℂ), ω₁ ≠ 0 → 0 < τ.im → IsPeriodLattice Λ ω₁ τ →
    2 * t₀ ∈ Λ → t₀ ∉ Λ →
    (∃! c : Fin 2 × Fin 2, IsEvenChar c.1 c.2 ∧ thetaChar c.1 c.2 (t₀ / ω₁) τ = 0) ∧
    0 < normSq1 Λ (th0 Λ t₀) ∧
    ∀ a b : Fin 2, IsEvenChar a b → thetaChar a b (t₀ / ω₁) τ = 0 →
      (normSq1 Λ (th0 Λ t₀))⁻¹ = Real.sqrt (2 * τ.im) * ‖thetaChar a b 0 τ‖ ^ 2

theorem thetaChar_eq_tsum (a b : Fin 2) (z τ : ℂ) :
    thetaChar a b z τ = ∑' n : ℤ, cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (z + ((b : ℕ) : ℂ) / 2)) := by
  unfold thetaChar jacobiTheta₂ jacobiTheta₂_term
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

theorem jacobiTheta₂_half (a b : Fin 2) (τ : ℂ) :
    jacobiTheta₂ ((((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ =
      cexp (-((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2) * thetaChar a b 0 τ := by
  unfold thetaChar
  rw [← mul_assoc, ← Complex.exp_add, zero_add, zero_add]
  have : -((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2 +
      ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (((b : ℕ) : ℂ) / 2)) = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

end GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic
