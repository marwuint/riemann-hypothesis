import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

noncomputable section

open Module Submodule

namespace GlobalTheory.Published

def SuccMinTransference : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ), 1 ≤ i → i ≤ n → succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n

namespace SuccMinTransference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SuccMinTransference

theorem SuccMinTransference.of_forall
    (h : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ), 1 ≤ i →
      i ≤ finrank ℝ E →
      succMin L i * succMin (dualLattice L) (finrank ℝ E - i + 1) ≤ finrank ℝ E) :
    SuccMinTransference := by
  intro n L _ _ i h1 hi
  simpa using h _ L i h1 (by simpa using hi)

end GlobalTheory.Published
