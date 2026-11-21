import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmithNormalFormExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smith_normal_form_exists : Smith := by
  exact @GlobalTheory.CompanionTheory.InertSmith.smith
