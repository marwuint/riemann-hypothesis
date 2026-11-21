import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_read_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRead := by
  exact @GlobalTheory.CompanionTheory.MixZ.existsRead
