import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.HodgeTateTest

open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage

variable {O : Type} [CommRing O]

noncomputable abbrev GmO (O : Type) [CommRing O] : Over (Spec (CommRingCat.of O)) :=
  Gm (Spec (CommRingCat.of O))

end GlobalTheory.HodgeTateTest
