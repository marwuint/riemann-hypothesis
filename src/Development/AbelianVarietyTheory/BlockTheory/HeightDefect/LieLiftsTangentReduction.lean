import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj

abbrev epsRed (R : Type) [CommRing R] : Sp R ⟶ Sp (DualNumber R) :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
