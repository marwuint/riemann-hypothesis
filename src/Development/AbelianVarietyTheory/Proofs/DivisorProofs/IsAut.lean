import Mathlib

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThK.Dbl

def opT {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (k : G → G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ h' in 𝓕, φ h' * k h h' ∂μ

def rconv {G : Type} [Mul G] [MeasurableSpace G] (μ : Measure G) (ψ : G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ g, ψ g * φ (h * g) ∂μ

def InSpan {G : Type} [Mul G] (f f' u u' : G → ℂ) : Prop :=
  ∃ (n : ℕ) (y : Fin n → G) (c : Fin n → ℂ),
    u = (fun h => ∑ j, c j * f (h * y j)) ∧ u' = (fun h => ∑ j, c j * f' (h * y j))

end GlobalTheory.ThK.Dbl
