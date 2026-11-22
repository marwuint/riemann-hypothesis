import Formalism.LFunctionBounds.PositivityBound

open Complex

noncomputable section

namespace Formalism.FX

open Classical

def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (x + y0 * I)) - (∫ x in x0..x1, g (x + y1 * I)) +
    I * (∫ y in y0..y1, g (x1 + y * I)) - I * (∫ y in y0..y1, g (x0 + y * I))

def RectResidue : Prop :=
  ∀ (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (x0 x1 y0 y1 : ℝ), x0 < x1 → y0 < y1 →
    (∀ p ∈ P, x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) →
    (∃ U : Set ℂ, IsOpen U ∧ (Set.uIcc x0 x1 ×ℂ Set.uIcc y0 y1) ⊆ U ∧ DifferentiableOn ℂ G U) →
    (∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) →
    rectInt g x0 x1 y0 y1 = 2 * Real.pi * I * ∑ p ∈ P, b p

end Formalism.FX
