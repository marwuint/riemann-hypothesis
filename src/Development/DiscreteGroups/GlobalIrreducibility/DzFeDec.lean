import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeMat

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem cyc_val : ((cyc g (m + 1) : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if i = finRotate (m + 1) k then 1 else 0 := rfl

def Hp (r : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = Fin.last m then r k else (1 : Mt g (m + 1)) i k

end DiscreteGroups.sglob.DzFe
