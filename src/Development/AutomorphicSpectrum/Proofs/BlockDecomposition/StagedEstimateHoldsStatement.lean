import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  exact @GlobalTheory.CompanionTheory.RgEis.stage
