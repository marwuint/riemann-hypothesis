import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.Diag MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham.MultGrp

section Coord

variable {S : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def coordVal (x : Sp A ⟶ (Gm S).left) : A :=
  charVal (Over.homMk x rfl : Over.mk (x ≫ (Gm S).hom) ⟶ Gm S) (ULift.up 1)

end Coord

variable {R : Type} [CommRing R]

end GlobalTheory.DeRham.MultGrp
