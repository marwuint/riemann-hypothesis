import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_norm_bound : PositivityTheory.RgBcC.Fc.SecBound := by
  exact @GlobalTheory.CompanionTheory.SecBd.secBound_main
