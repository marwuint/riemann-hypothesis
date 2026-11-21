import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Agree

variable {σ A : Type} [CommRing A]

def Agree (D : ℕ) (F G : MvPowerSeries σ A) : Prop :=
  ∀ n : σ →₀ ℕ, n.degree ≤ D → MvPowerSeries.coeff n F = MvPowerSeries.coeff n G

end Agree

end PI.UnitaryGroupMassFormula.PadicGainBound
