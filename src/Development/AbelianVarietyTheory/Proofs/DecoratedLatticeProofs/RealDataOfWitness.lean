import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LinkedPins

set_option maxHeartbeats 4000000 in

theorem seeAt_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : SeeAt (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 X h s) : SeeAt a.x.R.toRealDat a.x.F.lv2 X h s := by
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  refine ⟨hs.fin, ?_, ?_⟩
  · exact (hs.conj)
  · exact (hs.mat)

theorem setting_congr {D : D7} (M : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Prop)
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (e : F0 = F0') {P : SPack D F0} {P' : SPack D F0'} (hP : HEq P P')
    (h : M P'.X P'.inst) : M P.X P.inst := by
  subst e
  cases hP
  exact h

open Classical in

theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  have h : Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id := by
    funext P
    ext x
    exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x
  rw [h, Finset.image_id]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Fam.LinkedPins

