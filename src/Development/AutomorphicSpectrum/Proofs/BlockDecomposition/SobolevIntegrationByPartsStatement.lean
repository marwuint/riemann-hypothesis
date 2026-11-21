import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_integration_by_parts : PositivityTheory.RgBcC.Fc.IbpSob := by
  exact @GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob
