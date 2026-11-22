import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

end GlobalTheory.ClassSumPinLink
