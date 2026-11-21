import Mathlib

open NumberField NumberField.InfinitePlace

namespace Formalism.IndefR.Leaf.HaarTransferContinuity

variable (F : Type) [Field F] [NumberField F]

abbrev W := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // ¬ v.IsReal} → ℂ)

end Formalism.IndefR.Leaf.HaarTransferContinuity
