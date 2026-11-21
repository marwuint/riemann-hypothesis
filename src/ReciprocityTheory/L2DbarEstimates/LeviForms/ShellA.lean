import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

def shG {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) : V n :=
  WithLp.toLp 2 (fun i => g i (s y))

theorem shG_apply {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) (i : Fin n) :
    shG n g s y i = g i (s y) := rfl

end

end ReciprocityTheory.L2DbarEstimates.I
