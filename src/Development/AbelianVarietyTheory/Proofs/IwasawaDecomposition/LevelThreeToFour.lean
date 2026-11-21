import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStages
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsTiedSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeEEAndNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSetting
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDictGoodOpNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfMemSuppSpan

noncomputable section

namespace GlobalTheory.Mem.SRe.UpS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowHyp {D : D7} (p : RowPk D) : Prop :=
  p.R.toLevCh.Is p.A.μ0 ∧ p.R.grp_levels p.F ∧ GrpPin p.R ∧ p.R.IsModels ∧
    LinearMap.range p.eE = (p.R.EEat (p.R.levR p.F true)).comap p.R.HE.e ∧
    (∀ x, ‖p.eE x‖ ^ 2 = RealDat.nP p.F true * ‖x‖ ^ 2) ∧ DallTie p.R p.F

set_option maxHeartbeats 4000000 in

theorem rowHyp_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : R3.Pins R F cG)
    (hH : R3.Holds R F) : RowHyp (⟨G, Pl0, T, A3.A, Ks, R.toRealDat, F.lv2, Y.eE⟩ : RowPk D) := by
  have hr := R3.RowsLvl.range_eE_and_norm D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨plg, iso, h⟩ := hP.keep.grp
  exact ⟨hP.char.base.lev, hP.char.base.grp.levels, ⟨R.eG.trans cG, plg, iso, h⟩, hP.char.base.models, hr.1, hr.2, Y.dall⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem rowHyp_pkOf {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowHyp (pkOf r) :=
  (by with_unfolding_all exact ((rowHyp_read r.r.z.R r.r.z.F r.r.z.cG r.r.Y r.r.z.pins r.r.intersectionNumber_baseChange) :))

def reSt {C : Cols B} (a : Late B C) (Zs : SNew a.D) : SStage B C a.W := reStage a.st Zs

def SatNew : Prop :=
  ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u) (P : SPack a.D F0), GapHyp a.D →
    Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D →
    a.D.what₂.Dstar = StandardLattice.DstarD a.D → IdempotentRealFixed a.D → RowHyp p →
    ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁)

set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries (h1 : GlobalTheory.Dec.DSInfChar) (h2 : GlobalTheory.Published.HarishChandraFinite) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.DiscreteSeriesUpqUnique) (h5 : Formalism.L2.SG.RowsDef.RowsFinDim) : SatNew :=
  fun B C a p F0 P g i l r d e ⟨a1, a2, a3, a4, a5, a6, a7⟩ =>
    _root_.GlobalTheory.Mem.SRe.satOfDiscreteSeries h1 h2 h3 h4 h5 B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE P g i l r d a1 a2 a3 e a4 a5 a6 a7

set_option maxHeartbeats 8000000 in

theorem sat_col (a : w.Lt) (col : ColT w a) (p : RowPk (Late.D a)) (Zs : SNew (Late.D a))
    (H : ∀ (N : ∀ u, Submodule (𝓞 (Late.D a).what₂.LL) ((Late.D a).div.Nu u).V) (hh : (Late.D a).what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ (fun u => (col.C.forms u).to0) F₁ →
        Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁))
    (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (col' : ColT w (upL a (reSt a Zs) N h)) :
    Nonempty ((p.up a (reSt a Zs) N h).SAt fun u => (col'.C.forms u).to0) := by
  let Zn : New (Late.D a) := ⟨Zs, (by with_unfolding_all exact (N :)), (by with_unfolding_all exact (h :))⟩
  obtain ⟨C', hC⟩ := ColRe.exists_colsTiedSym (Late.D a) Zn col.C
  let F₀ : ∀ u, Forms0 (reD (Late.D a) Zn) u := fun u => (C'.forms u).to0
  let F₁ : ∀ u, Forms0 (reL a Zn).D u := (by with_unfolding_all exact (F₀ :))
  have hF : SameL a Zn (fun u => (col.C.forms u).to0) F₁ := (by with_unfolding_all exact (hC :))
  obtain ⟨s⟩ := H Zn.N Zn.h F₁ hF
  have c := CarModel.sameStd B f T w a Zn col ((by with_unfolding_all exact (col' :))) F₁ hF
  exact ⟨CarModel.satCar (D := Late.D (upL a (reSt a Zs) N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) (p.up a (reSt a Zs) N h) ((by with_unfolding_all exact (s :)))⟩

def RealOf : Prop := ∀ D : D7, VolTieG D → D.s.cdScale = Vol.trueScale D.cd → (∀ τ, D.dsig τ = Vol.trueDsig D.R (D.hc τ)) → RealTied D

def PackEx : Prop := ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
  ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I)

set_option maxHeartbeats 4000000 in

theorem real_of (hR : RealOf) (a : w.Lt) (g : GIs2 K w a.G) (hs : a.S.s.cdScale = Vol.trueScale a.G.cd)
    (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ)) : RealTied (w.D a) :=
  hR (w.D a) (g a.W a.V a.S a.N).1 ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :)))

theorem realOf (h1 : Vol.DiscreteSeriesExist) (h2 : Vol.FormalDegreeFormula₂) : RealOf := by
  intro D hv hs hd
  refine ⟨?_, ?_, ?_, hv⟩
  · rw [Vol.cdScaleTie_iff, hs]
    exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd
  · intro τ
    unfold Formalism.L2.Theta.IsDsig
    rw [hs, hd τ]
    exact (_root_.GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig h1 h2 D.cd D.R (D.hc τ)).1
  · intro τ H _ _ σ d hσ hf
    rw [hs] at hf
    rw [hd τ]
    exact (_root_.GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig h1 h2 D.cd D.R (D.hc τ)).2 H σ d hσ hf

theorem goodIdempotent_real_of_harishChandra_series (D : D7) (h : GlobalTheory.GLq.ESerTie D) : IdempotentRealFixed D :=
  GlobalTheory.GoodIdemReal.star_coeff_of_reverse D fun k g hm h0 x => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨L, -, he⟩ := h k
    rw [he, he]
    exact DFunLike.congr_fun (GlobalTheory.GLq.GalSer.eSerC_map L _ D.R.r hm (GlobalTheory.SeriesSupport.rel_dual L hm h0)) x

end GlobalTheory.Mem.SRe.UpS

end
