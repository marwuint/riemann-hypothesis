import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Polynomial NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.HT

def frobMin {k : Type} [Field k] [Fintype k] (A : AbVar k) : ℚ[X] := minpoly ℚ (toEnd0 A (frob A))

def Injective : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A B : AbVar k), IsSimple A → IsSimple B →
    (Isog A B ↔ frobMin A = frobMin B)

end GlobalTheory.HT
