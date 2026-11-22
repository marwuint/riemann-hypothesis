import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopContDiffOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem psiCapelli : PsiCapelliStatement n := fun _ε _lam T μ hμ Y _g hg => psiM_capelli T μ hμ Y hg

end ReciprocityTheory.ChartRestriction.DS.S7
