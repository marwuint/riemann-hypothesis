import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw
