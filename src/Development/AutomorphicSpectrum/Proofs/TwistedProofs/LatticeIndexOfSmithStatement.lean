import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmith
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  exact @GlobalTheory.CompanionTheory.InertIndex.latIndex
