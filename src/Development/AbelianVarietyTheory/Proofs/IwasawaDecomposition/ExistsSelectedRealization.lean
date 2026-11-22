import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwExtend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowPartFormsAndNonzeroVectorsEveryPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

local macro:max "kq% " e:term:max : term => `((by kexactB $e))

noncomputable section

namespace GlobalTheory.Mem.R3.SelectionPairing

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.IndefR.AutomorphicEvaluation

theorem pack_move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0') {P : SPack D F0} {P' : SPack D F0'}
    (hP : HEq P P') (Φ : ∀ F1 : ∀ u, Formalism.L2.Forms.Forms0 D u, SPack D F1 → Prop) (h : Φ F0' P') : Φ F0 P := by
  subst hF
  obtain rfl := eq_of_heq hP
  exact h

def spRead {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (b : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df)
    (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) (wU : D.what₂.Word → Dc.Mem)
    (bij : Function.Bijective wU) (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) : SPer Dc :=
  Formalism.IndefR.Cx.spOf (X := X) b Dc hK Gd (Equiv.ofBijective wU bij).symm (fun m => pw ((Equiv.ofBijective wU bij).symm m))
    (fun m i => D.eMu ((Equiv.ofBijective wU bij).symm m) (D.jN ((Equiv.ofBijective wU bij).symm m)
      (eNu ((Equiv.ofBijective wU bij).symm m)
        (Pi.single (Fin.cast (congrArg Dc.a (Equiv.ofBijective_apply_symm_apply wU bij m)).symm i) 1))))

theorem spRead_congr {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (b : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) (wU : D.what₂.Word → Dc.Mem)
    (bij : Function.Bijective wU) (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (wU' : D.what₂.Word → Dc.Mem) (bij' : Function.Bijective wU')
    (eNu' : ∀ u, (Fin (Dc.a (wU' u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (hW : HEq wU' wU) (hN : HEq eNu' eNu) :
    spRead X b Dc hK Gd pw wU bij eNu = spRead X b Dc hK Gd pw wU' bij' eNu' := by
  cases hW
  cases hN
  rfl

def zscRaw {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (F : Face3 D A3) (L : SizeData₂ D) (Del h0 : ℕ) (c : ℝ) : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 A3 F.P0 F.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs
    { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }

def Places {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA D (Yc D 0)) (c : ℝ) (s : Bool)
    (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX X)) : Prop :=
  ∀ (v : Tw s R.HE.H) (hx : R.HE.e (Tw.out v) ∈ R.EEat (R.levR F true)),
    sE v = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι g c ⟨R.HE.e (Tw.out v), hx⟩) ∧
      RealDat.nP F true * ‖sE v‖ ^ 2 = ‖v‖ ^ 2

theorem exists_places {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA D (Yc D 0)) (c : ℝ) (s : Bool)
    (hE : R.models_HE) (hc : 0 < c) (hev : EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι g c) :
    ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX X)), 0 < κ ∧ Places R F X Gd ι g c s κ sE := by
  obtain ⟨κ, sE, hκ, h⟩ := GlobalTheory.Mem.SJ.Place.exists_placement D G Pl0 T A Ks R F X Gd ι g c s hE hc hev
  exact ⟨κ, sE, hκ, fun v hx => ⟨(h v hx).1, (h v hx).2.1⟩⟩

section Args

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}

set_option maxHeartbeats 1000000 in

theorem zsc_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (L' : SizeData₂ (w.st Z).toD7) (Del h0 : ℕ) (c : ℝ)
    (h : a.Zsc = zscRaw (famT t) t.r.z.F L' Del h0 c) : x.F.Zsc = zscRaw x.A3 x.F L' Del h0 c := by
  obtain rfl := eq_of_heq hx
  clear hx
  cases a with
  | mk Dc' Sp' Zsc' lam err lam_eq x pack intersectionNumber_baseChange hκ' hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem sp_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (wU : (w.st Z).toD7.what₂.Word → (Dc (zsOf t.r.z.R t.r.z.F)).Mem) (bij : Function.Bijective wU)
    (eNu : ∀ u, (Fin ((Dc (zsOf t.r.z.R t.r.z.F)).a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V)
    (hD : a.Dc = Dc) (hS : HEq a.Sp Sp) (hW : HEq x.C.wU wU) (hN : HEq x.C.eNu eNu)
    (hz : Sp (zsOf t.r.z.R t.r.z.F) =
      spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (Dc (zsOf t.r.z.R t.r.z.F)) hK Gd pw wU bij eNu) :
    HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := X) (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) hK Gd
      x.wd (fun m => pw (x.wd m)) x.bR) := by
  obtain rfl := eq_of_heq hx
  clear hx
  subst hD
  obtain rfl := eq_of_heq hS
  clear hS
  cases a with
  | mk Dc' Sp' Zsc' lam err lam_eq x pack intersectionNumber_baseChange hκ' hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  kexactB heq_of_eq (hz.trans (spRead_congr X _ _ hK Gd pw wU bij eNu (kq% C'.wU) (kq% C'.bij) (kq% C'.eNu) (kq% hW) (kq% hN)))

set_option maxHeartbeats 1000000 in

theorem see_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0) ≃* X.B.I.GA)
    (g : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0)) (c κ : ℝ)
    (sE : Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (HHX X))
    (h : Places t.r.z.R.toRealDat t.r.z.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) κ sE) :
    ∃ sE' : Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) x.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (HHX X),
      HEq sE sE' ∧ Places x.R.toRealDat x.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) κ sE' := by
  obtain rfl := eq_of_heq hx
  clear hx
  cases a with
  | mk Dc' Sp' Zsc' lam err lam_eq x pack intersectionNumber_baseChange hκ' hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  refine ⟨(by with_unfolding_all exact (sE :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl sE :))
  · exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem read_cols (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp₀ : ∀ Zs, SPer (Dc Zs))
    (Zsc₀ : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3)
    (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((by with_unfolding_all exact (t.r.Y :)))) :
    ∃ (wU : (w.st Z).toD7.what₂.Word → (Dc (zsOf t.r.z.R t.r.z.F)).Mem) (_ : Function.Bijective wU)
      (eNu : ∀ u, (Fin ((Dc (zsOf t.r.z.R t.r.z.F)).a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V),
      HEq C₀.wU wU ∧ HEq C₀.eNu eNu := by
  refine ⟨(by with_unfolding_all exact (C₀.wU :)), (by with_unfolding_all exact (C₀.bij :)), (by with_unfolding_all exact (C₀.eNu :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl C₀.wU :))
  · exact (by with_unfolding_all exact (HEq.refl C₀.eNu :))

set_option maxHeartbeats 1000000 in

theorem see_cast (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (Dc : DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 (zsOf t.r.z.R t.r.z.F))) (S : SPer Dc)
    (wU : (w.st Z).toD7.what₂.Word → Dc.Mem) (bij : Function.Bijective wU)
    (eNu : ∀ u, (Fin (Dc.a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V)
    (hz : S = spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) Dc hK Gd pw wU bij eNu)
    (sE : Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (HHX X)) :
    ∃ sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] S.HH, HEq sEE sE := by
  subst hz
  refine ⟨(by with_unfolding_all exact (sE :)), ?_⟩
  exact (by with_unfolding_all exact (HEq.refl sE :))

set_option maxHeartbeats 2000000 in

theorem selection_group_ambient_tie (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (hA : AmbAre t.r.Z ex.amb ex.amb0) (hM : MjAre t.r.Z Yd)
    (hG : GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG))
    (hp : ∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v)
    (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp₀ : ∀ Zs, SPer (Dc Zs))
    (Zsc₀ : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3)
    (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((by with_unfolding_all exact (t.r.Y :))))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (ι : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0)) (c : ℝ) (hc : 0 < c)
    (hev : EvalTieT (t.r.z.R.toRealDat.MY 0) t.r.z.R.toRealDat.ν0 t.r.z.R.toRealDat.fd0
      (t.r.z.R.toRealDat.EEat (t.r.z.R.toRealDat.levR t.r.z.F.lv2 true)) X Gd ι g c)
    (L' : SizeData₂ (w.st Z).toD7) (Del h0 : ℕ) (c' : ℝ) :
    ∃ (a : TwArgs ex t) (x : R3.TwIn ex), HEq a.x x ∧ a.Dc = Dc ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧
      x.F.Zsc = zscRaw x.A3 x.F L' Del h0 c' ∧
      HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := X) (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) hK Gd
        x.wd (fun m => pw (x.wd m)) x.bR) ∧
      ∃ (κ : ℝ) (sE' : Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) x.R.toRealDat.HE.H →ₗ⋆[ℂ]
          Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (HHX X)),
        HEq x.sEE sE' ∧ 0 < κ ∧ Places x.R.toRealDat x.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) κ sE' := by
  obtain ⟨wU, bij, eNu, hw0, hn0⟩ := read_cols (ex := ex) (t := t) Dc Sp₀ Zsc₀ C₀
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer (Dc Zs), Sp (zsOf t.r.z.R t.r.z.F) =
      spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (Dc (zsOf t.r.z.R t.r.z.F)) hK Gd pw wU bij eNu := by
    classical
    exact ⟨Function.update Sp₀ (zsOf t.r.z.R t.r.z.F) _, Function.update_self _ _ _⟩
  obtain ⟨κ, sE, hκ, hsE⟩ := exists_places t.r.z.R.toRealDat t.r.z.F.lv2 X Gd ι g c
    (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.pins.char.base.models.HE hc hev
  obtain ⟨sEE, hsEE⟩ := see_cast (ex := ex) (t := t) X hK Gd pw _ _ wU bij eNu hSp sE
  obtain ⟨a, haDc, haSp, haZsc, haSEE, haWU, haENu, -⟩ := _root_.GlobalTheory.Mem.R3.twArgs_exists hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp
    Dc Sp₀ Zsc₀ C₀ Sp (zscRaw (famT t) t.r.z.F L' Del h0 c') sEE
  obtain ⟨x, hx⟩ : ∃ x : R3.TwIn ex, HEq a.x x := ⟨a.x, HEq.rfl⟩
  have hW : HEq x.C.wU C₀.wU := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haWU :))
  have hN : HEq x.C.eNu C₀.eNu := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haENu :))
  have hE : HEq x.sEE sEE := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haSEE :))
  obtain ⟨sE', h1, h2⟩ := see_pin a x hx X Gd ι g c κ sE hsE
  exact ⟨a, x, hx, haDc, hW, hN, zsc_pin a x hx L' Del h0 c' haZsc,
    sp_pin a x hx X hK Gd pw Dc Sp wU bij eNu haDc haSp (hW.trans hw0) (hN.trans hn0) hSp,
    κ, sE', (hE.trans hsEE).trans h1, hκ, h2⟩

end Args

end GlobalTheory.Mem.R3.SelectionPairing

end

