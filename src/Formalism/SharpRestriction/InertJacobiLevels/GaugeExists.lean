import Formalism.SharpRestriction.InertJacobiLevels.ExtraNew
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
import Formalism.SharpRestriction.InertJacobiLevels.ExtraEnt
import Formalism.LocalRingCardinality.DataMink

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure Shape (D : D7) : Prop where
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
  gatM : ∀ u w h, (D.gat u w h).M = ⊥
  gatComp : ∀ u w h, Nonempty ((D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
  gatTr : ∀ u w h (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
    (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D}
  {K : G.Consts} {X : DivX D} {cX : ExtraC}

end Formalism.MainNotions.Inhab

end
