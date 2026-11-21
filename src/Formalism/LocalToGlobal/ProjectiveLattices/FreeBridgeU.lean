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

theorem trivCls_eq : PjFree.trivCls Xo c = Formalism.L2.Pj.trivCls Xo c := rfl

variable {Xo c}

def QPt.toPj (q : PjFree.QPt Xo c) : Formalism.L2.Pj.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

def QPt.ofPj (q : Formalism.L2.Pj.QPt Xo c) : PjFree.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

theorem QPt.ofPj_toPj (q : PjFree.QPt Xo c) : QPt.ofPj q.toPj = q := rfl

theorem QPt.toPj_ofPj (q : Formalism.L2.Pj.QPt Xo c) : (QPt.ofPj q).toPj = q := rfl

theorem ordQ_toPj (q : PjFree.QPt Xo c) (f : Rul Xo c) :
    Formalism.L2.Pj.ordQ Xo c q.toPj f = PjFree.ordQ Xo c q f := rfl

variable (Xo c)

theorem valSet_alg_eq (la : HeightOneSpectrum (𝓞 c.F)) :
    PjFree.valSet Xo c (PjFree.algCls Xo c) la = Formalism.L2.Pj.valSet Xo c (Formalism.L2.Pj.algCls Xo c) la := rfl

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

theorem nabUniq_iff : PjFree.NabUniq Xo c ↔ Formalism.L2.Pj.NabUniq Xo c := Iff.rfl

theorem frBaseChg_eq : @PjFree.FrBaseChg = @Formalism.L2.Pj.FrBaseChg := rfl

theorem reFrame_eq : @PjFree.ReFrame = @Formalism.L2.Pj.ReFrame := rfl

theorem xoNumPt_eq : @PjFree.XoNumPt = @Formalism.L2.Pj.XoNumPt := rfl

theorem locFld_eq : @PjFree.LocFld = @Formalism.L2.Pj.LocFld := rfl

theorem tanLin_eq : @PjFree.TanLin = @Formalism.L2.Pj.TanLin := rfl

theorem sClause_eq : @PjFree.SClause = @Formalism.L2.Pj.SClause := rfl

theorem intRebase_eq : @PjFree.IntRebase = @Formalism.L2.Pj.IntRebase := rfl

end Formalism.L2.PjFree
