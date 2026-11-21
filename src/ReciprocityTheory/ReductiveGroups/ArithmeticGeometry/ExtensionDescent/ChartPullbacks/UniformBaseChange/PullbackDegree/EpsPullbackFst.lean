import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.UBC

open Semi

section Adj

theorem homEquiv_mul {S S' : Scheme.{0}} (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

theorem toBase_eq_symm {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj A) :
    toBase (pullback.condition : pullback.fst A.hom f ≫ A.hom = pullback.snd A.hom f ≫ f) x =
      ((Over.mapPullbackAdj f).homEquiv T A).symm x := by
  rfl

end Adj

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

end ReciprocityTheory.ChartRestriction.G.Out.UBC
