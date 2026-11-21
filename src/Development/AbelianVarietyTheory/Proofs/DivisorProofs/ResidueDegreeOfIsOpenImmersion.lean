import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.CurveDegreesCompare

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f ≫ g).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank _ _ _).symm

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)
  let e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

end GlobalTheory.CurveDegreesCompare
