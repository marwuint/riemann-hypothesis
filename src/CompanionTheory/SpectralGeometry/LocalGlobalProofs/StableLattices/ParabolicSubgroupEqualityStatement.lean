import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ParabolicSubgroupEquality : CompanionTheory.RgExh.Dec.N.S.PSubEq := by
  exact @GlobalTheory.CompanionTheory.PSubFlag.psubEq
