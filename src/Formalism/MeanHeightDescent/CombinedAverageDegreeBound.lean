import Mathlib
import Formalism.MeanHeightDescent.BadRowsNumeric

open Finset

noncomputable section

namespace Formalism.ExtensionFiltration

def CombinedAverageDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (T D A cs X cc z ρ R1 R2 Bn δ' : ℝ)
    (h sl δ dc degc : ι → ℝ) (LL0 U b Ca Cb PPf e1 e2 muU : ℝ),
    0 ≤ D → 3 * D + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c) →

    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →

    (∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2)
      ≤ degc c) →

    T * X ≤ Ca * LL0 * U + e1 → T * cc ≤ Cb * LL0 * U + e2 →
    cs * (6 * D + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →

    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →
    -(2 * ((Ca + Cb) * LL0 * U + b / 4)) ≤ muU

end Formalism.ExtensionFiltration
