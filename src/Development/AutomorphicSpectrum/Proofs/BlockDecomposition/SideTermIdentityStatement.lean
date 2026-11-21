import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_identity : StdGood → BdetLaw → SideOf := by
  exact @GlobalTheory.CompanionTheory.MirSides.sideOf
