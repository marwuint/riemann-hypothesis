import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes

open ReciprocityTheory.ChartRestriction.G.Semi

structure IsAbelianScheme {S : Scheme.{u}} (A : Over S) [GrpObj A] : Prop where
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geometricallyConnected : GeometricallyConnected A.hom
  comm : IsCommMonObj A

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
