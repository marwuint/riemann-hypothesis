import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.SharpRestriction.InertJacobiLevels.ExtraH
import Formalism.LocalRingCardinality.SpanPowerMembership.WithSeenTauOf

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

structure Shape0 (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  cls0 : ∀ u μ, Nonempty ((D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0)

variable {D : D7}

structure LevGapD (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau)
  tau_def : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT)
    (x : 𝓞 D.host.F), x ∈ (errX.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D (tau u w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

open Classical in

def seenOf (D : D7) (X : ErrX D) : D.what₂.Word → D.what₂.places.Pl → Bool :=
  fun u w => decide (∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def LevGapD.recS (G : LevGapD D) : D7 := withSeen D (seenOf D G.errX) G.tau

end Formalism.MainNotions.Inhab

end
