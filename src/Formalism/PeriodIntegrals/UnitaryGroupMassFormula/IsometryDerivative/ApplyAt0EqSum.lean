import Mathlib
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm

open Finset

noncomputable section

namespace PI.IsoDerivBFintype

open PI.IsoDerivB

section main

variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)

instance fintypeCC (n : ℕ) : Fintype (ColChoice (Lt := Lt) n nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin n))

variable [Fintype T]

end main

end PI.IsoDerivBFintype
