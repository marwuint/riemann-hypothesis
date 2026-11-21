import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight MvPolynomial
open scoped nonZeroDivisors Classical

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def conjId (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity
