import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP
