import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB

theorem ofDeg_X (D : DegPre R) (hB : D.TauBimult) : (ofDeg D hB).X = D.X := rfl

theorem ofDeg_c (D : DegPre R) (hB : D.TauBimult) (a : D.X) : (ofDeg D hB).c a = D.c a := rfl

end GlobalTheory.PolDeg
