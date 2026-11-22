import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0Three
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeFrameAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AntiOfStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinned0OfGap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PtRowsAt

section General

open NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

def Placed {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧
    RowJ R eE P.X P.inst P.G t S.j

theorem Placed.of_heq {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {eE : D.what₂.EE →ₗ[ℂ] R.HE.H}
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0') {P : SPack D F0} {S : SRest P} {P' : SPack D F0'} {S' : SRest P'}
    (hP : HEq P P') (hS : HEq S S') {t : GA D (D.sp.Y 0)} {c : ℝ} (h : Placed R F eE P' S' t c) : Placed R F eE P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  exact h

set_option maxHeartbeats 1000000 in

theorem placed_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (h : Placed R.toRealDat F.lv2 eE P S t c) :
    Placed ((R.updS k lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 eE P S t c :=
  ⟨⟨h.1.fin, h.1.conj, h.1.mat⟩, h.2.1, h.2.2⟩

set_option maxHeartbeats 1000000 in

theorem exAt_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (h : R.toRealDat.ExAt) :
    ((R.updS k lam).withErr e).toRealDat.ExAt :=
  ⟨h.ItY, h.ItX, h.ioY, h.ioX, h.Th, h.ioP, h.thF, h.thG⟩

section Args

open GlobalTheory.Mem.Top.Bl

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}

set_option maxHeartbeats 1000000 in

theorem exAt_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) : x.R.toRealDat.ExAt := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.ExAt) a.pack
  exact e.mpr (exAt_upd _ _ _ _ t.exAt)

set_option maxHeartbeats 1000000 in

theorem placed_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 (w.st Z).toD7 u} (P : SPack (w.st Z).toD7 F0) (S : SRest P)
    (g : GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0)) (c : ℝ)
    (h : Placed (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE P S g c) :
    Placed x.R.toRealDat x.F.lv2 x.Y.eE P S g c := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, F, _⟩ => ∀ eE : (w.st Z).toD7.what₂.EE →ₗ[ℂ] R.HE.H, HEq eE t.r.Y.eE →
        Placed R.toRealDat F.lv2 eE P S g c) a.pack
  refine e.mpr (fun eE he => ?_) _ a.eE
  obtain rfl : eE = t.r.Y.eE := eq_of_heq he
  exact placed_upd _ _ _ _ _ _ _ _ _ _ _ _ _ h

end Args

end General

theorem gapHyp_of_hd {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl) (H : GlobalTheory.Core.Rk.HD D L C' Cl Cg cb Cu cT CT) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  refine ⟨hr, fun τ j hj => ?_⟩
  have := GlobalTheory.Core.Rk.HdGap.gap_of HL τ j.1 hj
  simp only [Fin.eta] at this
  have key : (((16 : ℚ) * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    rw [Rat.cast_sub]; push_cast; linarith
  exact_mod_cast key

end GlobalTheory.Fam.PtRowsAt

end
