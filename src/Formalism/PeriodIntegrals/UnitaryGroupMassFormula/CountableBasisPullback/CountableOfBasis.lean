import Mathlib
import Formalism.PeriodIntegrals.ThGDefs

open MeasureTheory

namespace PI.NormPullGW

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

instance haarIJ : (volume : Measure (I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : I => (volume : Measure (J → ℂ)))

instance haarTIJ : (volume : Measure (T → I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : T => (volume : Measure (I → J → ℂ)))

end PI.NormPullGW
