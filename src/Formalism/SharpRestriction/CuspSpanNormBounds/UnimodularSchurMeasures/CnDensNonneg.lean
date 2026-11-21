import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Finset
open scoped ENNReal

abbrev cn_Root (a : ℕ) : Type :=
  ({p : Fin a × Fin a // p.1 < p.2} ⊕ {p : Fin a × Fin a // p.1 < p.2}) ⊕ (Fin a ⊕ Fin a)

def cn_la {a : ℕ} (t : Fin a → ℝ) : cn_Root a → ℝ
  | .inl (.inl p) => t p.1.1 / t p.1.2
  | .inl (.inr p) => t p.1.1 * t p.1.2
  | .inr (.inl x) => t x ^ 2
  | .inr (.inr x) => t x

def cn_dim {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : cn_Root a → ℕ
  | .inl (.inl p) => 2 * j p.1.1 * j p.1.2
  | .inl (.inr p) => 2 * j p.1.1 * j p.1.2
  | .inr (.inl x) => j x ^ 2
  | .inr (.inr x) => 2 * j x * n0

def cn_dens {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (t : Fin a → ℝ) : ℝ := ∏ r, cn_la t r ^ (cn_dim j n0 r * f)

end Formalism.MainNotions.LeviCoordinates

end
