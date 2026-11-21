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

theorem det_hm (b : Fin (m + 1) → ZMod g) : (Hm b : Mt g (m + 1)).det = b 0 := by
  have hl : (Hm b : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
    intro i k hik
    have hik' : i < k := hik
    have hk : k ≠ 0 := fun h => by subst h; exact absurd hik' (Fin.not_lt_zero i)
    simp [Hm, hk, Matrix.one_apply, ne_of_lt hik']
  rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_succ]
  simp [Hm, Fin.succ_ne_zero]

def hmGL (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hm b) (by rw [det_hm]; exact hb)

theorem hmGL_val (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : ((hmGL b hb : Gn g (m + 1)) : Mt g (m + 1)) = Hm b :=
  rfl

end DiscreteGroups.sglob.DzFe
