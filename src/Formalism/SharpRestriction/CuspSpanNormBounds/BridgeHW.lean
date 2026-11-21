import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

noncomputable section

namespace Formalism.MainNotions.BridgeHW

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem highest_weight_exists_bis [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] : DiscreteSeriesWeylDimension.HighestWeightExists := Fact.out

variable {eps : ℝ} (Fm : FamP eps)

end Formalism.MainNotions.BridgeHW

end
