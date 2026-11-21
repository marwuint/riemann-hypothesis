import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_finite_dimensional : GlobalTheory.CompanionTheory.EGlue.PairFD := by
  exact @GlobalTheory.CompanionTheory.EGlue.pairFD_holds
