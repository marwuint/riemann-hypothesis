import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

instance MultiRing.isDomain_series (K : Type) [Field K] (r : ℕ) : IsDomain (MvPowerSeries (Fin r) K) :=
  GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r

end GlobalTheory.LocM.FJ
