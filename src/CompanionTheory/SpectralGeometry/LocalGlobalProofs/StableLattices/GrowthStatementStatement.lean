import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.GrowthStatement : CompanionTheory.RgExh.Dec.L.Growth := by
  exact @GlobalTheory.CompanionTheory.PathGrowth.growth
