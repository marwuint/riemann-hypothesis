import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  exact @GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet
