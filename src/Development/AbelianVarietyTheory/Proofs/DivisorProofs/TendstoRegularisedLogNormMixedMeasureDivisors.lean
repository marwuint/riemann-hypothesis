import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.LogLim

theorem compactSpace_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem nsq_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) (y : CxPts p σ) : 0 ≤ N.φ.nsq (secVal p σ t) y := by
  unfold Weight.nsq; positivity

theorem continuous_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) : Continuous (N.φ.nsq (secVal p σ t)) :=
  continuous_iff_continuousAt.2 fun y => ((_root_.GlobalTheory.Mix.SecNorm.logSec_basic k X p σ N t).2.2.1 y).continuousAt

theorem exists_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (N : MLine p σ) (t : N.B.Sec) : ∃ C : ℝ, ∀ y, N.φ.nsq (secVal p σ t) y ≤ C := by
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hp
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_nsq N t)).bddAbove
  exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩

end GlobalTheory.Mix.LogLim

open GlobalTheory.Mix.LogLim in

theorem GlobalTheory.Mix.tendsto_logReg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  intro hP F _ X _ _ p σ e hp hdim N t
  set w := N.φ.nsq (secVal p σ t) with hw_def
  have hbasic := _root_.GlobalTheory.Mix.SecNorm.logSec_basic F X p σ N t
  have hcont : Continuous w := continuous_nsq N t
  obtain ⟨C, hC⟩ := exists_nsq_le hp N t
  have hwC : ∀ y, 0 ≤ w y ∧ w y ≤ C := fun y => ⟨nsq_nonneg N t y, hC y⟩
  refine ⟨fun hgen L => ?_, fun L Δ hΔ => ?_⟩
  · have hfin := (_root_.GlobalTheory.MixFin.finite_and_intg hP F X p σ (e + 1) hp hdim L).1
    have hint := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hp hdim L N t hgen
    have one (ε : ℤˣ) (hi : Integrable (N.logSec t) (part L ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w y + 1 / ((n : ℝ) + 1)) ∂part L ε) atTop
          (𝓝 (2 * ∫ y, Real.log (w y) / 2 ∂part L ε)) := by
      haveI := hfin ε
      have hnull := _root_.GlobalTheory.MixNull.part_compl_null F X p σ σ.injective hp (e + 1) L ε (nonzeroLocus t) hgen
      refine _root_.GlobalTheory.Mix.tendsto_integral_log_add_inv _ (part L ε) w C hcont.measurable hwC ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
      exact fun h => hy ((hbasic.2.1 y).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    simp only [Mix.int, MLine.logSec, mul_sub]
    exact h1.sub h2
  · haveI : CompactSpace X := compactSpace_of_proj hp
    have hS := Δ.finite_support_mult
    have hsub (f : X → ℝ) : Function.support (fun z => (Δ.mult z : ℝ) * f z) ⊆ ↑hS.toFinset := by
      intro z hz
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hz; simp [h0]
    have hrw : (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z) =
        fun n : ℕ => ∑ z ∈ hS.toFinset, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z :=
      funext fun n => finsum_eq_sum_of_support_subset _ (hsub _)
    rw [hrw, finsum_eq_sum_of_support_subset _ (hsub _), Finset.mul_sum]
    refine tendsto_finset_sum _ fun z hz => ?_
    have hz0 : Δ.mult z ≠ 0 := by simpa using hz
    have hcoh := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hdz := (_root_.GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hp hdim z).1 hcoh
    obtain ⟨hfin, -, hnull, hlog⟩ := _root_.GlobalTheory.CycFin.cycle_facts hP F X p σ hp e L z hdz
    have hzt := hΔ z hz0
    have hint := hlog N t hzt
    set π := ptMap (closι z) rfl σ with hπ
    have hπc : Continuous π := continuous_of_comp (f := closι z) fun _ => rfl
    have one (ε : ℤˣ) (hi : Integrable (fun y => N.logSec t (π y)) (part (fun i => (L i).pull (closι z) rfl) ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w (π y) + 1 / ((n : ℝ) + 1)) ∂part (fun i => (L i).pull (closι z) rfl) ε)
          atTop (𝓝 (2 * ∫ y, Real.log (w (π y)) / 2 ∂part (fun i => (L i).pull (closι z) rfl) ε)) := by
      haveI := hfin ε
      refine _root_.GlobalTheory.Mix.tendsto_integral_log_add_inv _ _ (fun y => w (π y)) C (hcont.comp hπc).measurable (fun y => hwC (π y)) ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus t) hzt ε))
      exact fun h => hy ((hbasic.2.1 (π y)).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    have := (h1.sub h2).const_mul (Δ.mult z : ℝ)
    simp only [cycInt, Mix.int, MLine.logSec] at this ⊢
    convert this using 2
    ring
