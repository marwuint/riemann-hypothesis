import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem emb_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (x : H.E) :
    H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) := by
  exact H.conjE_apply (H.emb g) x

end Formalism.L2.Host
