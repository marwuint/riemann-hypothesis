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

theorem cyc_inv_val : (((cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) =
    Matrix.of fun i k => if finRotate (m + 1) i = k then 1 else 0 := rfl

def Hp (r : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = Fin.last m then r k else (1 : Mt g (m + 1)) i k

theorem hp_lower (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
  intro i k hik
  have h : i < k := hik
  have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le h (Fin.le_last k))
  simp [Hp, hi, Matrix.one_apply_ne (ne_of_lt h)]

theorem det_hp (r : Fin (m + 1) → ZMod g) : (Hp r : Mt g (m + 1)).det = r (Fin.last m) := by
  rw [Matrix.det_of_lowerTriangular _ (hp_lower r), Fin.prod_univ_castSucc]
  simp [Hp, (Fin.castSucc_lt_last _).ne]

def hpGL (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hp r) (by rw [det_hp]; exact hr)

theorem hpGL_val (r : Fin (m + 1) → ZMod g) (hr : r (Fin.last m) ≠ 0) :
    ((hpGL r hr : Gn g (m + 1)) : Mt g (m + 1)) = Hp r := rfl

end DiscreteGroups.sglob.DzFe
