import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_weight_of_torus_facts : PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.BetaWeight := by
  exact @GlobalTheory.CompanionTheory.TorusSymbol.betaWeight
