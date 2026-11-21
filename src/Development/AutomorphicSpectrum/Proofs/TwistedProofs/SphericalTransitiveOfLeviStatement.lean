import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans := by
  exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists
