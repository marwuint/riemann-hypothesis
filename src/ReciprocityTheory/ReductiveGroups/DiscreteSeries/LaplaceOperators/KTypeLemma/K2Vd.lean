import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DualLowestKTypeOfStandard

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem k2Vd (n : ℕ) : EigenspaceWeightConeDual n :=
  TwistedDualLemmas.dualLowestKType_of_standard (k2V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
