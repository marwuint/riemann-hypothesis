import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsLow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitReps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsExtGeometryTupleOfRepresentatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCoset
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTameStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowJoin

open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem idxProd (hI : I.Ok) (hT : I.IsTw) (a : I.ι) : IdxProd I.sel (I.tup a) (I.cst a) (I.idx a) := by
  have h := hI.idx_ok a
  rw [(hT a).2] at h ⊢
  exact _root_.GlobalTheory.TwBridge.idxProd_twIdx _ _ _ _ _ _ _ _ _ _ h

theorem h_one (hT : I.IsTw) (a : I.ι) : ∀ j b (P : BadPr I a), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1 := by
  rw [(hT a).2]
  exact Formalism.L2.Col.twSt_h_g I.Ch I.sel (I.tup a) (I.cst a) _

theorem get_bij {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} (hA : A.Is) (j : ℕ) (hj : j + 1 < B.R.m) :
    Function.Bijective fun β : Ch₀ j => (A.b0 j β).get (by omega) := by
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = fun _ => ∅ := fun p => by
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj.ne] at h
    funext P
    rw [cosetIn, show p.1.2 = ∅ from h]
    simp
  refine ⟨fun β β' e => hA.chart_ext j (by omega) β β' ?_ ((h0 _).trans (h0 _).symm), fun b => ?_⟩
  · rw [← (A.b0 j β).of_get (by omega) (by omega), ← (A.b0 j β').of_get (by omega) (by omega)]
    exact congrArg (Idx.of · _) e
  · haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
    letI := B.fields.starE
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := j) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    refine ⟨A.chOf j ((I.stp u a j).cl (Idx.of b (by omega)) p), ?_⟩
    exact Idx.get_eq (congrArg Subtype.val (hA.rep j (by omega) _).1.symm) _

section Place

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}

structure Good (P : BadPr I a) (G : QGeo v Bs PP) {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk)
    (sg : ℂ) : Prop where
  sign : sg = 1 ∨ sg = -1
  tw : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  up : ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j))
  rat : ∀ j d h, Nonempty ((I.idx a).β j) → E.A j d h =
    {g | ∃ b, IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z))) ((I.idx a).h j b P) g}
  next : ∀ j d (h : j + 1 + d = G.s), Nonempty ((I.idx a).β j) → (E.A (j + 1) d h).Nonempty →
    ∃ γ : Formalism.L2.Col.AutY B.fields B.R (j + 1), Bdd (B.primes X) (j + 1) P.1 γ ∧
      ∃ al, Formalism.L2.Col.FiniteSumNonzeroLargeDepth I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j al P) γ

set_option maxHeartbeats 1000000 in

theorem exists_good (hI : I.Ok) (hT : I.IsTw) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs) (G : QGeo v Bs PP) (heq : PP = P.1) (hc : c.Is)
    (hstd : IsStdChar (I.rec7 l Z) c.ψ (-1)) (χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle)
    (hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (χ j) (I.C.mu0 ⟨j, hj⟩ * I.xi a)) :
    ∃ (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ), Good P G E hψ sg := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hcp : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ := heq ▸ G.compl
  have hid : Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) G.q.e P.1 := heq ▸ G.idem
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split (I.rec7 l Z) G.k (ofSplit G.q) c.ψ hstd
  choose μ hμ using fun j => hcomp (χ (j - 1))⁻¹
  have hψ := continuous_of_cond G.cond
  have hd := TC.degOne_of_ok hI a P
  obtain ⟨⟨ϖ, unif, ψ, cont, cond, δ, tame, η, unr, sg⟩, hA, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_completionTwistData_chainColumns _ _ _ _ _ _ _ _ _ _ _ hL P hP G.k (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ hcp G.unif G.ψk hψ G.cond
      (_root_.GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp (I.rec7 l Z) G.k G.q P.1 hid hd.1 hd.2 hcp.int c.ψ hstd G.ψk G.char) μ
      fun i hi => GlobalTheory.T.step_inverse_character_local_component_chain_tame I hI l Z a P hP G.k G.q hid hcp.int hcp.dense i hi (χ i) (hχ i hi) _ (hμ (i + 1))
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  have hM : G.s + 1 ≤ (I.cst a).M := by
    rw [hT.cst_eq]
    show _ ≤ B.R.m
    omega
  obtain ⟨A, a1, a2, a3, a4⟩ := exists_system G.unitVol hA hL (idxProd hI hT a) hM
  have hmu : ∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ) := fun j hj => by
    rw [h3 j (by omega)]
    exact hμ (j + 1)
  obtain ⟨E₀, rfl, rfl, rfl, e4⟩ := _root_.GlobalTheory.QExtEx.exists_qExt _ c v Bs _ G χ hc δ tame η unr hmu A a1 _ a2
  obtain ⟨E, e1, e2, e3, e5, -, e6⟩ := _root_.GlobalTheory.QTw.CosExt.exists_qExt_cos _ c v Bs _ G χ hc _ tame _ unr hmu _ a1 _ a2 (E₀.Ch (G.s + 1))
    (fun y => (E₀.cos y).out ∘ id) (fun y y' h => E₀.cos_inj y y' (by
      rw [← e4] at h
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using h))
    (fun z hz => by
      rw [← e4] at hz ⊢
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using E₀.cos_all z hz)
  refine ⟨E, hψ, sg, h4, ?_, e5, e6, e3 ▸ a3, e3 ▸ a4⟩
  have e7 : E.tw hψ sg = ⟨G.ϖ, unif, G.ψk, cont, cond, E₀.δ, tame, E₀.η, unr, sg⟩ := by simp only [QExt.tw, e1, e2]
  rw [e7]
  exact hA

theorem res_of_tw (hI : I.Ok) {hP : PP ∈ Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)} {G : QGeo v Bs PP} {W : TwData G.k}
    (h : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL ⟨PP, hP⟩ (G.q.pr.comp (incA (I.rec7 l Z))) G.s W)
    {ξ : (kP PP)ˣ →* ℂˣ} (hξ : IsRes (I.xi a) PP ξ) : G.Res W.δ ξ := by
  intro z x r hx hr
  have h0 : (z : (I.rec7 l Z).host.E) ≠ 0 := fun e => x.ne_zero (by rw [hx, e]; exact (G.q.pr.comp (incA (I.rec7 l Z))).map_zero)
  have h1 : Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E) = (r : kP PP) := (Formalism.L2.Col.reduction_coe PP z).trans hr.symm
  have h2 : IsUnit (Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E)) := h1 ▸ r.isUnit
  have h3 : Formalism.L2.Col.IntAt PP (z : (I.rec7 l Z).host.E) :=
    ⟨z, 1, fun e => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 e), by simp⟩
  have h4 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads a)
    (GlobalTheory.Mem.ReadTwist.tameAt (hI.xi_reads a) fun v => Subgroup.mem_iInf.1 (I.tup a).2.1.2 v) PP h2.unit z (Units.mk0 _ h0) rfl
    (hr.symm.trans h1.symm)
  refine Units.ext ((h.del _ x h3 h2 hx).trans ?_)
  rw [hξ z (Units.mk0 _ h0) r rfl hr, Units.val_inv_eq_inv_val]
  exact congrArg _ ((congrArg _ (dif_pos h2)).trans h4)

end Place

end GlobalTheory.LowJoin

end
