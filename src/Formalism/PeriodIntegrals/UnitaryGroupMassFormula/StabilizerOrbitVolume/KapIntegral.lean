import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ESSymmApply

noncomputable section

namespace PI.VolStabSW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

end PI.VolStabSW.RPA
