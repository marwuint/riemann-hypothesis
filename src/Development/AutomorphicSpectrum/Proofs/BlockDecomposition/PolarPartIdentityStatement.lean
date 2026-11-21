import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  exact @GlobalTheory.CompanionTheory.RswPolar.polar
