import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

def bad (g r p : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (irrDeg g p ×ˢ monicDeg g (r - p)).image (fun x => x.1 * x.2)

end PI.SqfPrimeFactor.W
