import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.S

structure TwGap (D : D7) where
  ntw : NTw D.R D.host D.what₂ D.LL0 D.nd
  nexp : NExp D.R D.host D.what₂ D.LL0 D.nd ntw
  nth : NTh D.R D.host D.what₂ D.LL0 D.nd ntw nexp
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E (ntw.l i) →
    LocBridge (ntw.l i) D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (ntw.O0 i)

  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (ntw.l i))
    (x : D.nd.Om), x ∈ D.nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g D.nd, D.what₂.embLL ((nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g
  cover : NTw.TwCover ntw

def withTw (D : D7) (W : TwGap D) : D7 :=
  { D with ntw := W.ntw, nexp := W.nexp, nth := W.nth, ntwbr := W.ntwbr, ntwbr_ind := W.ntwbr_ind, nStage_trivialCharacter_coeff_eq := W.nStage_trivialCharacter_coeff_eq }

end Formalism.BasicNotions.Examples₂
