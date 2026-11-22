import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTauFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedEqDatTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLatticesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := _root_.GlobalTheory.TrueTau.exists_trueTau N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

section Install

variable {x : St P} {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host} {hf eig θ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) hf eig θ} {hF}
  (p : PreTie (ysOf Bs) (datTw x N₁).geo.v₀ Bs.exp hF Pq)

abbrev kwP : TwNew (DN x N₁) := keepTw (DN x N₁) p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP : SideB (DN x (nP p)) (((kwP p).cf cf)) (((kwP p).row Rw)) (lowAll (DN x (nP p))) ((Pq)) (sP p) ((hf)) ((eig))
    ((θ)) :=
  (by with_unfolding_all exact ((keepSideB (DN x N₁) p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs) :))

end Install

end GlobalTheory.HeightCounting.SerCopy

end
