import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

set_option autoImplicit false

open CategoryTheory

namespace GlobalTheory.Vert.Flag

variable {X : AlgebraicGeometry.Scheme.{0}} {E : X.Modules} {N : ℕ}

def SameStep (fl fl' : Flag E N) (i : Fin (N + 1)) : Prop :=
  ∃ e : fl.F i ≅ fl'.F i, e.hom ≫ fl'.ι i = fl.ι i

end GlobalTheory.Vert.Flag
