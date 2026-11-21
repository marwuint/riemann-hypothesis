import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

def GeneratesFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  ∀ x : F, ∃ r s : O, β s ≠ 0 ∧ x * β s = β r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

end GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs
