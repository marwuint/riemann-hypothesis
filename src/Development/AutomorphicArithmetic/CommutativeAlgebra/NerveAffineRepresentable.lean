import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedByUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.LevelRep

noncomputable section

variable {D : Type} [CommRing D] {d p : ℕ}

private theorem rel_iff {A : Type} [CommRing A] {x y : (Vec D d).obj A} :
    (Vec D d).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

end

end UpperTheory.LevelRep

