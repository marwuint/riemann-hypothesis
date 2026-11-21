import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackward
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeBackward : CompanionTheory.RgExh.Hk.Back := by
  exact @GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back
