import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rgExh_flagFacts : CompanionTheory.RgExh.Dec.N.S.FlagFacts := by
  exact @GlobalTheory.CompanionTheory.GradFlag.flagFacts
