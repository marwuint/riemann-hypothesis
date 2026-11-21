import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi

namespace GlobalTheory.MiS.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem used_base (P : RowSideFamily ex) : Formalism.IndefR.RecTie.Used0 D (P.I.tup P.A3.A.μ0) := Or.inl P.tied.div.tup.mu0

theorem mu_eq_of_heq (P : RowSideFamily ex) {Zs : DefSub P.A3.fam3.amb3} (h : Zs = P.Zs)
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Zs)) (hS : HEq S P.S0) : S.μ = P.S0.μ := by
  subst h
  rw [eq_of_heq hS]

end GlobalTheory.MiS.Check

end
