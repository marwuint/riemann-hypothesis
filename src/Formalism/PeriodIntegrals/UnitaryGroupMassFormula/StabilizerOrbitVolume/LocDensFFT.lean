import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS

noncomputable section

namespace PI.VolStabSW

namespace FiniteFieldCounting

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

end FiniteFieldCounting

end PI.VolStabSW
