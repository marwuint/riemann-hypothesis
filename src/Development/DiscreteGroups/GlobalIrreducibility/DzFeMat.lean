import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzFeSv
import Development.DiscreteGroups.GlobalIrreducibility.DzFeOrth

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

abbrev SIdx (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}

def Um (N : SIdx m → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = k then 1 else if h : i < k then N ⟨(i, k), h⟩ else 0

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

end DiscreteGroups.sglob.DzFe
