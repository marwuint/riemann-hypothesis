import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas
