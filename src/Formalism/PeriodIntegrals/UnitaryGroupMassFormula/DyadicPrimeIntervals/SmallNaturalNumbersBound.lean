import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop

namespace PI.PrimesDyadicRS.K

open Real

def D (h : ℕ) : ℕ := Nat.primeCounting h - Nat.primeCounting (h / 2)

end PI.PrimesDyadicRS.K
