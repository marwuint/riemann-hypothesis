import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_total_of_products : ProdTh → ProdMeas → StepTotal := by
  exact @GlobalTheory.CompanionTheory.ThTot.stepTotal
