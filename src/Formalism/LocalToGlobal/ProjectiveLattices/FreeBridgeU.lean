import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
import Formalism.LocalToGlobal.ProjectiveLattices.UniqFree
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

def QPt.toPj (q : PjFree.QPt Xo c) : Formalism.L2.Pj.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

def QPt.ofPj (q : Formalism.L2.Pj.QPt Xo c) : PjFree.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

variable (Xo c)

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

end Formalism.L2.PjFree
