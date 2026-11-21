import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  exact @GlobalTheory.CompanionTheory.LinAlg.twoBases
