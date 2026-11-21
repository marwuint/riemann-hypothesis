import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

theorem dim_eq (p : PtAt ex Csz) (i : Fin D.R.m) :
    (p.P.A3.indefDown p.P.S0).dW i = Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i) := by
  have hz := p.zs
  have hs := p.s0
  have key : ∀ (Z : DefSub p.P.A3.fam3.amb3) (S : IndefData (p.P.A3.side3 p.P.P0 p.P.ψ0 Z)), Z = p.P.Zs → HEq S p.P.S0 →
      p.P.S0.dW i = S.dW i := by
    intro Z S h1 h2
    subst h1
    rw [eq_of_heq h2]
  exact key _ _ hz hs

end GlobalTheory.ExportPin.Model
