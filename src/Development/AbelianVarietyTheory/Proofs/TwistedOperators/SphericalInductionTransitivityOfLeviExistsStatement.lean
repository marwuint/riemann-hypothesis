import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalInductionTransitivity_of_leviExists : LeviExists → SphTrans := by
  exact @GlobalTheory.InertZeta.sphTrans
