import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ), sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  exact @GlobalTheory.PolarU.SinhcPres.sAd_pY
