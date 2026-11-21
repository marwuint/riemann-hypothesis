import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_of_rational : GlobalTheory.CompanionTheory.MixZ.CycleOfRat := by
  exact @GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat
