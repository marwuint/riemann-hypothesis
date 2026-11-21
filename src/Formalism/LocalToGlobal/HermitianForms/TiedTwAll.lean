import Formalism.LocalToGlobal.HermitianForms.TiedTwSame
import Formalism.LocalToGlobal.HermitianForms.TiedTwJ
import Formalism.LocalToGlobal.HermitianColumns.TiedQCHost

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

structure TwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTied D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJoint ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTied D Tw ch cols.forms
  lv : TwistedLevelData forms

  same : TwLvSame forms

  lvJ : TwistedJointForms ch cols.forms

end Formalism.L2.Forms

end
