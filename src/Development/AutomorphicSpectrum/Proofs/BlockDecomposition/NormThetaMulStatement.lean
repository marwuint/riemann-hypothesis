import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_bound_alt : CountBd := by
  exact @GlobalTheory.CompanionTheory.MassCount.countBd
