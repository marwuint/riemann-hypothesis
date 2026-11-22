import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def Hm (b : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if k = 0 then b i else (1 : Mt g (m + 1)) i k

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

end DiscreteGroups.sglob.DzFe
