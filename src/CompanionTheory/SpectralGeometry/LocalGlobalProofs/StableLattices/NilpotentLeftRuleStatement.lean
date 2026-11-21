import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentLeftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  exact @GlobalTheory.CompanionTheory.PathCoef.leftRule
