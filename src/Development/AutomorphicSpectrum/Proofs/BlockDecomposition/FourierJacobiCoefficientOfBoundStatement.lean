import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound
