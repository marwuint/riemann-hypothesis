import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv
