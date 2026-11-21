import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

noncomputable section

open Module Submodule

namespace GlobalTheory.Published

def SuccMinTransference : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ), 1 ≤ i → i ≤ n → succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n

namespace SuccMinTransference

end SuccMinTransference

end GlobalTheory.Published
