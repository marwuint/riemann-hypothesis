import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  exact @GlobalTheory.CompanionTheory.WordFam.exhaust
