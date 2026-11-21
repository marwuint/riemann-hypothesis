import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv
