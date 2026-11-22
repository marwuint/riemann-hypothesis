import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)

def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z

end Formalism.HermitianLattices.WeilRepresentation
