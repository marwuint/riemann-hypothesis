import Formalism.LocalToGlobal.ProjectiveLattices.GenValInjPf

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def SepXSt : Prop := IsSeparated Xo.s

variable {Xo c}

end Formalism.L2.Pj
