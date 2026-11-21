import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LeviDecompositionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists := by
  exact @GlobalTheory.CompanionTheory.InertLevi.leviExists
