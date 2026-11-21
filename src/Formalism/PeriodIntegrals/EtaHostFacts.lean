import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PI.EtaHostFacts

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def Unram : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1

end PI.EtaHostFacts
