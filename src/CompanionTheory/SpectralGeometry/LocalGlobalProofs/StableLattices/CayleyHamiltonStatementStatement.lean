import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CayleyHamiltonHk : CompanionTheory.RgExh.Hk.CayleyHam := by
  exact @GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam
