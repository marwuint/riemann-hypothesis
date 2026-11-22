import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def HasUnif (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) G, P.TorsionIso

variable (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end General

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
