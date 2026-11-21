import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma toMK_one' (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma toMK_mul' {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ Kset ε := k.2

end ReciprocityTheory.ChartRestriction.DS.S7
