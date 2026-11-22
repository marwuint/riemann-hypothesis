import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt

open Finset MeasureTheory Filter Topology
open Formalism.LogVandermondeBounds.StandardLattice
open scoped ComplexOrder

noncomputable def cloudV (c Δ : ℝ) : ℕ → ℝ := fun l => c - 4 * Δ * l

end Formalism.HermitianLattices.FormalDegreeBoundsAlt
