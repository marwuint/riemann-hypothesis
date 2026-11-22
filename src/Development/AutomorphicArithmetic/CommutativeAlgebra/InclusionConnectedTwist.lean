import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

noncomputable section

namespace UpperTheory.SimplicialRelationHom

variable (D : Type) [CommRing D]

private def Rg : RF where
  obj A _ := D →+* A
  map f x := f.comp x
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel x y := x = y
  map_rel _ _ _ h := by rw [h]

private def forget (N : ℕ) : (Vec D N).Hom (Rg D) where
  app _ _ x := x.1.1
  nat _ _ := rfl

variable {D}

private theorem rel_iff {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} :
    (Vec D N).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

end UpperTheory.SimplicialRelationHom

end
