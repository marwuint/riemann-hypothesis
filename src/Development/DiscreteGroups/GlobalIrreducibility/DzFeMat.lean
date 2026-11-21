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

theorem um_upper (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).BlockTriangular id := by
  intro i k hik
  have hik' : k < i := hik
  simp [Um, ne_of_gt hik', not_lt_of_gt hik']

theorem det_um (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (um_upper N)]
  simp [Um]

def umGL (N : SIdx m → ZMod g) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Um N) (by rw [det_um]; exact one_ne_zero)

theorem umGL_val (N : SIdx m → ZMod g) : ((umGL N : Gn g (m + 1)) : Mt g (m + 1)) = Um N := rfl

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

end DiscreteGroups.sglob.DzFe
