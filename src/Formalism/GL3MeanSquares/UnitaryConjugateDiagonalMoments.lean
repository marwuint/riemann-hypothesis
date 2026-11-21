import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt

open Finset MeasureTheory Filter Topology
open Formalism.LogVandermondeBounds.StandardLattice
open scoped ComplexOrder

def SW_density_tail : Prop :=
  ∀ (q : ℝ) (M : ℕ), 2 ≤ q → 3 ≤ M →
    HasSum (fun j : ℕ => q ^ (j + 1) * (1 - 1 / q) * (q⁻¹) ^ ((j + 1) * M))
      ((1 - 1 / q) * (q⁻¹) ^ (M - 1) / (1 - (q⁻¹) ^ (M - 1))) ∧
    (1 - 1 / q) * (q⁻¹) ^ (M - 1) / (1 - (q⁻¹) ^ (M - 1)) ≤ 4 / 3 * (q⁻¹) ^ (M - 1)

noncomputable def cloudV (c Δ : ℝ) : ℕ → ℝ := fun l => c - 4 * Δ * l

end Formalism.HermitianLattices.FormalDegreeBoundsAlt
