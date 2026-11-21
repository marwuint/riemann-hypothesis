import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFree_ringOfIntegers_of_isTorsionFree_int' : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N], Module.IsTorsionFree (𝓞 E) N := by
  exact @GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int
