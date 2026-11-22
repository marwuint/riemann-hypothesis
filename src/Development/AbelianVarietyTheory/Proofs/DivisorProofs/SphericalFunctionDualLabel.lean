import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

noncomputable section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.InvTranspose

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def flipM (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := A.transpose.submatrix Fin.rev Fin.rev

theorem flipM_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : flipM A i j = A j.rev i.rev := rfl

theorem flipM_mul (A B : Matrix (Fin n) (Fin n) R) : flipM (A * B) = flipM B * flipM A := by
  unfold flipM
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm

theorem flipM_one : flipM (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp [flipM_apply, Matrix.one_apply, eq_comm]

def theta : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), flipM (g : Matrix (Fin n) (Fin n) R),
    by rw [← flipM_mul, Units.mul_inv, flipM_one], by rw [← flipM_mul, Units.inv_mul, flipM_one]⟩
  map_one' := by
    apply Units.ext
    simp [flipM_one]
  map_mul' g h := by
    apply Units.ext
    simp only [mul_inv_rev, Units.val_mul, flipM_mul]

end Ring

end GlobalTheory.InvTranspose

end
