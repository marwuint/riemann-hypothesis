import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip
