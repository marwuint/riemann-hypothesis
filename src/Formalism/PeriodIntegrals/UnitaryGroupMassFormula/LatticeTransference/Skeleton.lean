import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.TransferenceKey
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Minima

open Module

namespace PI.Tr

theorem key_of (hL : KeyLarge) (hS : KeySmall) : PI.TransferenceKey := by
  intro E _ _ _ Λ _ _ lam u hlam hu
  rcases Nat.lt_or_ge (finrank ℝ E) 2 with h | h
  · exact hS E Λ lam u (by omega) hlam hu
  · exact hL E Λ lam u h hlam hu

theorem transferenceCover_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceCover := PI.cover_of_key (key_of (hG hP) hS)

theorem transferenceMinima_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceMinima := PI.minima_of_key (key_of (hG hP) hS)

end PI.Tr
