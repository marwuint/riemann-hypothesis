import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  exact @GlobalTheory.CompanionTheory.InertZeta.addVec
