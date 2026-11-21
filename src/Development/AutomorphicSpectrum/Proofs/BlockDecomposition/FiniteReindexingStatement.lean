import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_reindexing : PositivityTheory.Rg.BcB.G8.Fin.Reindex := by
  exact @GlobalTheory.CompanionTheory.SecReindex.reindex
