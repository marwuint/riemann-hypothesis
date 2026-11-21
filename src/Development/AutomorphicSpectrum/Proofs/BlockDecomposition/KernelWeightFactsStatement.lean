import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  exact @GlobalTheory.CompanionTheory.KerWord.kerW
