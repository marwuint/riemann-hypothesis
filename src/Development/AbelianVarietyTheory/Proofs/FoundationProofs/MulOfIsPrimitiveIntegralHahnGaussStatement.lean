import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω), Prim A P → Prim A Q → Prim A (P * Q) := by
  exact @GlobalTheory.Glue.Prim.mul
