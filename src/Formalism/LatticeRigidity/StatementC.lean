import Mathlib

namespace Formalism.SA.C

open Finset Real

noncomputable def chebPt (α β : ℝ) (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (α + β) / 2 + (β - α) / 2 * Real.cos (π * (j : ℕ) / n)

open NumberField in

def BoxSum : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), b ≠ 0 →
    ∀ (x : InfinitePlace E → ℝ) (Θ Kx : ℝ), (∀ w, 0 < x w) → 2 < Θ → 3 ≤ Kx →
      Θ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm b : ℝ) / ∏ w, x w →
      ∀ S : Finset E, (∀ l ∈ S, l ∈ b ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
          (C * Θ ^ (-(Kx - 5/2))) ^ Fintype.card (InfinitePlace E)

end Formalism.SA.C
