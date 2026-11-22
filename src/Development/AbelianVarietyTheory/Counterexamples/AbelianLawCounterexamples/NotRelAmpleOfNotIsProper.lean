import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTest

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem dim_eq_of_nonempty {S : Scheme.{0}} (s : S) (P : PolAV S) {n : ℕ}
    (h : SmoothOfRelativeDimension n P.A.hom) : P.g = n :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h (eSec P.A s)

end GlobalTheory.PolTest
