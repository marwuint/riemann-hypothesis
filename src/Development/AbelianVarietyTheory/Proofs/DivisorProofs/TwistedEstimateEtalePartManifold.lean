import Mathlib
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
import ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSetEtaleStein
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHolomorphicIffChartHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinLogGrowthWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightSingularWeightSmoothLeviNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientHolomorphicMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionHolomorphicMulFrameExtendByZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralWeightedAtlasFrameEtaleTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateRhsLeManifold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedL2EstimateTwistedSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateLhsTransfer

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.twisted_estimate_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → 300 ≤ T → IsCut T θ → (∀ y, y ∉ A.zeroSet s → δ * psi A L s y ≤ -T + 1 → y ∈ Ω) → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∃ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F ∧ ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu ≤ 30 * ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ _ ι La _ A E L s hs hsq δ hδ hlev Λ τ z β hdat Ω h T θ hhd hT hθ hΩcov hfin
  obtain ⟨hτ, hpos, hz, hβ, _hdense, C, hC0, hC⟩ := hdat
  obtain ⟨hΩ, hh, hh0⟩ := hhd
  obtain ⟨X, hXz, hXe⟩ := _root_.GlobalTheory.nzEtaleStein n Y ι La A Λ τ z hτ hpos hz
  have hU : IsOpen (nz A τ) := hz.isOpen
  have hpt := GlobalTheory.OTY.TwEst.nz_facts A L Λ s τ C hC0 hsq hC
  obtain ⟨hsmφ, hsmψ, hlevi⟩ := _root_.GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg n Y ι La A E L s hs δ hlev (nz A τ) z β hz hβ
    (fun y hy => (hpt y hy).1)
  obtain ⟨hqd, hqm, hq⟩ := _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable n Y ι La A (A.kap + E) (nz A τ) Ω β h hU hΩ hβ hh hh0
  have hψm : Measurable (psi A L s) :=
    (_root_.GlobalTheory.OTY.measurable_nsq_extend_and_psi n Y ι La A (A.kap + E) Ω h hΩ hh hh0).2 L s hs
  have htr := _root_.GlobalTheory.OTY.TwEst.lintegral_frame_transfer n Y ι La A E (nz A τ) z β hz hβ
  have hGholo : ∀ e : OpenPartialHomeomorph (nz A τ) (V n), IsChart n X.z e →
      DifferentiableOn ℂ ((fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) := by
    rw [hXz]
    exact (_root_.GlobalTheory.OTY.holo_etale_iff_holo_chart n Y ι La A (nz A τ) z hz Ω (GlobalTheory.OTY.TwEst.quot A h β) hΩ).2 hqd
  have hGm : Measurable (fun y : nz A τ => GlobalTheory.OTY.TwEst.quot A h β y) := by
    have h1 := hqm.comp (measurable_subtype_coe : Measurable (Subtype.val : nz A τ → Y))
    convert h1 using 1
    funext y
    simp only [Function.comp, GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
  have hθc : Continuous θ := hθ.1.continuous
  have hθb : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1 := hθ.2.2.2.1
  have hwint := _root_.GlobalTheory.OTY.TwEst.cutoff_quot_wint_le n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ θ hθc hθb
  obtain ⟨F0, hF0, hest⟩ := _root_.GlobalTheory.LogGrowth.twisted_extension_logGrowth n (nz A τ) X
    (fun y => GlobalTheory.OTY.TwEst.wt A E β z y) (fun y => psi A L s y)
    (fun y => GlobalTheory.OTY.TwEst.quot A h β y) (Subtype.val ⁻¹' Ω) δ T θ
    (by rw [hXz]; exact hsmφ) (by rw [hXz]; exact hsmψ) (fun x => (hpt x x.2).2.1) hδ hT hθ
    (by rw [hXz]; exact hlevi) (hΩ.preimage continuous_subtype_val) hGm hGholo
    (fun x hx => hΩcov x (hpt x x.2).1 hx)
    ⟨n, n * Real.log C, fun x => by rw [hXe]; exact (hpt x x.2).2.2⟩
    (by rw [hXz]; exact lt_of_le_of_lt hwint hfin)
  rw [hXz] at hF0 hest
  obtain ⟨hFsec, hFm⟩ := _root_.GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable n Y ι La A (A.kap + E) (nz A τ) z β F0 hz hβ hF0
  refine ⟨fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 (nz A τ) F0 y, hFsec, ?_⟩
  exact (_root_.GlobalTheory.OTY.TwEst.lhs_transfer n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T θ F0 hθc hFm).trans_le
    (hest.trans (mul_le_mul_of_nonneg_left
      (_root_.GlobalTheory.OTY.TwEst.rhs_le_manifold n Y ι La A E L s (nz A τ) z β h hU htr hq hqm hψm δ T) (by norm_num)))
