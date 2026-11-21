import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaSectionsClosedFibre

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section General

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {N : LB Y}

def IsSmul (r : R) (s s' : LB.Sec N) : Prop :=
  ∀ j : N.ι, s'.f j = resTop (N.U j) (scal p r) * s.f j

def Generates (s : LB.Sec N) : Prop :=
  ∀ s' : LB.Sec N, ∃ r : R, IsSmul p r s s'

end General

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaSectionsClosedFibre
