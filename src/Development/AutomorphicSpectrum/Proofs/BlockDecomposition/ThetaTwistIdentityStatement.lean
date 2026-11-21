import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_twist_identity : ThTwist := by
  exact @GlobalTheory.CompanionTheory.ThTw.thTwist
