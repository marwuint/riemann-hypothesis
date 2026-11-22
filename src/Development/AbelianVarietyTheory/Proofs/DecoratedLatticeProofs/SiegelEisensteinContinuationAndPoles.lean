import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegrableBoundDoublingIntegrandQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfolding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPoint
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaContinues_of_eisRegularAt {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {Φ : ℂ → GA D (dblSp V) → ℂ} (hE : EisContinues V Φ)
    (ha : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf (V.rank / 2))) (hreg : ∀ s₀, ∃ k, EisRegularAt V Φ s₀ k)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂)
    (hZ : IsZetaFamily V μ m Φ f₁ f₂) : ZetaContinues V μ m Φ f₁ f₂ := by
  obtain ⟨C', c, hio⟩ := _root_.GlobalTheory.Cont.HeightIo.height_io_bound D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := _root_.GlobalTheory.Core.Rk.Dom.exists_integrable_bound_dblIntegrandQ D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  exact ⟨hZ, Z, hext⟩

end GlobalTheory.Eis
