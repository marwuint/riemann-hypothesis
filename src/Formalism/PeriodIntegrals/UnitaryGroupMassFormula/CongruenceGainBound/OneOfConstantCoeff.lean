import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.AddPreservesExpCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.PowMod

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section AgreeSum

variable {σ A : Type} [CommRing A]

theorem Agree.add {D : ℕ} {F F' G G' : MvPowerSeries σ A} (hF : Agree D F F') (hG : Agree D G G') :
    Agree D (F + G) (F' + G') := fun n hn => by rw [map_add, map_add, hF n hn, hG n hn]

end AgreeSum

end PI.UnitaryGroupMassFormula.PadicGainBound
