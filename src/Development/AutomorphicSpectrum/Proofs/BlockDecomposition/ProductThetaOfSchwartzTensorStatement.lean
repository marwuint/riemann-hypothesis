import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor
