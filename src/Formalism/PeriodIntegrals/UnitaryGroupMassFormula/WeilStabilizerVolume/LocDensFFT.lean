import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFS

noncomputable section

namespace PI.VolStabW

namespace FiniteFieldCounting

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

end FiniteFieldCounting

end PI.VolStabW
