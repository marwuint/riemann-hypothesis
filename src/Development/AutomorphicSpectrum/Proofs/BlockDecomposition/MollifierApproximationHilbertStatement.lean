import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll
