import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  exact @GlobalTheory.CompanionTheory.FcCls.clsFacts
