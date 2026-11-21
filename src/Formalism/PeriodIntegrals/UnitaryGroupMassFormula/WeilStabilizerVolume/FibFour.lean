import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibOfTens

noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology

section Four

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

def IsCcOn (U : Set V) (φ : V → ℝ) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

end Four

end PI.VolStabW
