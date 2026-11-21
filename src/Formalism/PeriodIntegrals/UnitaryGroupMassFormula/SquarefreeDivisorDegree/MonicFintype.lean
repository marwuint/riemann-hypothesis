import Mathlib
import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfDivDeg.W

instance monicFintype (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Fintype {p : (ZMod g)[X] // p.Monic ∧ p.natDegree = n} :=
  Fintype.ofEquiv _ ((monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv).symm

end PI.SqfDivDeg.W
