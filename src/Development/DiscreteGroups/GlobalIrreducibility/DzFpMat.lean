import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil
import GroundTheory.AutomorphicForms.FiniteBruhat

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

section Ring

variable {R : Type} [CommRing R]

theorem columnMatrix_sq_zero {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) :
    Matrix.of (fun r k : Fin n => if k = c then a r else 0) * Matrix.of (fun r k : Fin n => if k = c then a r else 0) =
      0 := by
  ext r k
  simp [Matrix.mul_apply, ha]

def colElt {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) : GL (Fin n) R :=
  ⟨1 + Matrix.of (fun r k => if k = c then a r else 0), 1 - Matrix.of (fun r k => if k = c then a r else 0),
    by rw [add_mul, one_mul, mul_sub, mul_one, columnMatrix_sq_zero a c ha, sub_zero]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, columnMatrix_sq_zero a c ha, add_zero]; abel⟩

end Ring

end DiscreteGroups.sglob.DzFp
