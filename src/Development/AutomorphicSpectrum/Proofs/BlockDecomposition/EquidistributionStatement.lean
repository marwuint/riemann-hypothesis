import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  exact @GlobalTheory.CompanionTheory.Equi.equi
