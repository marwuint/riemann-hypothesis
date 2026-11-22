import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.BasicNotions.Examples₂

def withSeen (D : D7) (seen : D.what₂.Word → D.what₂.places.Pl → Bool)
    (tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau)) : D7 :=
  { D with
    fm := fun u => { D.fm u with seenP := seen u, tauOf := tau u }
    eMu_isom := D.eMu_isom
    nuIn := D.nuIn
    nuIn_inj := D.nuIn_inj
    nuIn_range := D.nuIn_range
    nuIn_jN := D.nuIn_jN
    nuIn_norm := D.nuIn_norm
    s_Cu_isom := D.s_Cu_isom }

end Formalism.BasicNotions.Examples₂
