import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_coefficient_total : ZeroTotal := by
  exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal
