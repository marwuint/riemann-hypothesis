import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def ImHGenusOne : Prop :=
  ∀ (d x0 x1 y0 y1 : ℝ), 0 < d →
    (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).im /
        (Real.sqrt d / 2) = x1 * y0 - x0 * y1 ∧
    2 * (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).re =
        2 * (x0 * y0 + x0 * y1 + (1 + d) / 4 * (x1 * y1)) + (x1 * y0 - x0 * y1)

def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)

def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z

end Formalism.HermitianLattices.WeilRepresentation
