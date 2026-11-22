import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff

noncomputable section

namespace GlobalTheory.LocM.Cht.GoodOfZero

section Fibre

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end Fibre

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

end GlobalTheory.LocM.Cht.GoodOfZero
