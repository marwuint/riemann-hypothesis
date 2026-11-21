import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

variable {Sh : Shape}

def ETI.ty (t : ETI Sh) : ℕ := t.2.2.2.2.val

def ETI.IsB (t : ETI Sh) : Prop := t.ty = 1 ∧ t.2.2.2.1 = 0

instance (t : ETI Sh) : Decidable t.IsB := inferInstanceAs (Decidable (_ ∧ _))

end PI.UnitaryGroupMassFormula.PadicGainBound
