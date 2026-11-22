import Mathlib

open Finset

noncomputable section

namespace Formalism.ExtensionFiltration

def MeanHeights : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (h sl : ι → ℝ) (cs cc ρ X : ℝ),
    0 ≤ ρ → ρ ≤ 1 → 0 ≤ X →
    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →
    max 0 ((1 - ρ) * cs - X - cc) ≤ (∑ c, (h c + cs)) / (Fintype.card ι : ℝ)

def SumComponents : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (T D A cs X cc z ρ R1 R2 Bn δ' : ℝ)
    (h δ dc degc : ι → ℝ),
    0 ≤ D → 3 * D + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c) →
    (∀ c, -cs ≤ h c) →
    (∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2)
      ≤ degc c) →
    max 0 ((1 - ρ) * cs - X - cc) ≤ (∑ c, (h c + cs)) / (Fintype.card ι : ℝ) →
    -(T * (X + cc)) - cs * (6 * D + 10 + T * (z + 2 * ρ)) - (A * Real.log (max A 1) + 4) - R1
        - 2 * z * R2 ≤ (∑ c, degc c) / (∑ c, dc c)

end Formalism.ExtensionFiltration
