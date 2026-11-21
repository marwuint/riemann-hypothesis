import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
open IsLocalRing

open MvPolynomial

namespace GlobalTheory.RootAdjoin

variable {R : Type} [CommRing R] {r : ℕ} (n : ℕ) (x : Fin r → R)

noncomputable abbrev rel : Ideal (MvPolynomial (Fin r) R) :=
  Ideal.span (Set.range fun i => X i ^ n - C (x i))

lemma algebraMap_eq_mk (z : R) :
    algebraMap R (MvPolynomial (Fin r) R ⧸ rel n x) z = Ideal.Quotient.mk (rel n x) (C z) := rfl

end GlobalTheory.RootAdjoin
