import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm

open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  exact @GlobalTheory.ConvSeries.hasSum_term_integral
