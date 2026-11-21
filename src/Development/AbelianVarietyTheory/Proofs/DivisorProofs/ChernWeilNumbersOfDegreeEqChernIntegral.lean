import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := _root_.GlobalTheory.ChernCalc.isForm_evalF_chernF F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := _root_.GlobalTheory.ChernCalc.isMetricFr_pullGram F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using _root_.GlobalTheory.ChernCalc.graded_weight F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [_root_.GlobalTheory.ChernCalc.chernTopPart_eq_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (_root_.GlobalTheory.LineForm.wInt_props _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (_root_.GlobalTheory.ChernCalc.fibre_integral F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [_root_.GlobalTheory.LineForm.pullback_evalF _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.ChernCalc.pullback_chernF F σ X Y ι m E E' φ f hf hR H hH) R,
      _root_.GlobalTheory.ChernCalc.integral_chernF_mul_grF F σ Y ι m E' _ hM, e]
    exact _root_.GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
