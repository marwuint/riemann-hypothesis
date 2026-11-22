import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.LinkLev

theorem spack_X_eq_of_heq {D : D7} {F F' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F = F') (P : GlobalTheory.Mem.SRe.SPack D F)
    (P' : GlobalTheory.Mem.SRe.SPack D F') (h : HEq P P') : P.X = P'.X := by
  subst hF
  rw [eq_of_heq h]

theorem conjLevel_of_setting_eq {D : D7} (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X')
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : Formalism.L2.Theta.GA D (D.sp.Y 0) ≃* X.B.I.GA) (hι : ι = (Formalism.L2.SG.RowsJoinPinned.iotaX X h).toMulEquiv)
    (t t' : Formalism.L2.Theta.GA D (Yc D 0)) (ht : t = t') (J : Set (Formalism.L2.Theta.GA D (Yc D 0)))
    (χ : Formalism.L2.Theta.GA D (Yc D 0) → ℂ)
    (hc : Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ J χ (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X')
      (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X' (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' k))) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ J χ (ι ⁻¹' seeKS X) (fun k => seeChiS X (ι k)) := by
  subst hX
  subst hι
  subst ht
  exact hc

theorem of_setting_eq {D : D7}
    (P : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.L2.Theta.GA D (D.sp.Y 0) → Prop)
    (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X') (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)) (ht : t = t') (hP : P X' h' t') :
    P X h t := by
  subst hX
  subst ht
  exact hP

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levels_withErr_updS (R : RealDat3 D A3 Ks) (kap : ℝ) (lam e) (F : Face3 D A3) (Dc Sp Zsc)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt ((R.updS kap lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X h t) ↔
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (GlobalTheory.Mem.SRe.JR R.toRealDat F.lv2) (GlobalTheory.Mem.SRe.chiR R.toRealDat F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt R.toRealDat F.lv2 X h t) := Iff.rfl

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem levels_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (x : TwIn ex) (ax : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (GlobalTheory.Mem.SRe.JR t.r.z.R.toRealDat t.r.z.F.lv2) (GlobalTheory.Mem.SRe.chiR t.r.z.R.toRealDat t.r.z.F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt t.r.z.R.toRealDat t.r.z.F.lv2 X h s) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 X h s := by
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact (levels_withErr_updS _ _ _ _ _ _ _ _ _ _ _).2 hs

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

end GlobalTheory.Mem.R3.LinkLev
