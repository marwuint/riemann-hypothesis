import Mathlib

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

section Poly

variable (R : Type*) [CommRing R]

def blockWt (N n : ℕ) : Fin N × Fin n → (Fin N → ℕ) := fun p => Pi.single p.1 1

def shear {N n : ℕ} (i j : Fin N) :
    MvPolynomial (Fin N × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin N × Fin n) R) :=
  aeval fun p => Polynomial.C (X p) +
    (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)

def H {N n : ℕ} (ν : Fin N → ℕ) : Submodule R (MvPolynomial (Fin N × Fin n) R) :=
  weightedHomogeneousSubmodule R (blockWt N n) ν ⊓
    ⨅ (i : Fin N) (j : Fin N) (_ : i < j),
      LinearMap.ker ((shear R i j).toLinearMap -
        (IsScalarTower.toAlgHom R (MvPolynomial (Fin N × Fin n) R)
          (Polynomial (MvPolynomial (Fin N × Fin n) R))).toLinearMap)

end Poly

end Formalism.NormUnitaryCountingLemmas
