import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_exists : Completion := by
  exact @GlobalTheory.CompanionTheory.InertDoubling.completion
