import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def TateCharPolySt : Prop := EndCharPolySt

end GlobalTheory.Published

namespace GlobalTheory.TateCharPoly

end GlobalTheory.TateCharPoly
