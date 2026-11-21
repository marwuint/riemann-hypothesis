import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.LocFub

open GlobalTheory.CxForm

def headL (n : ℕ) : V (n + 1) →L[ℂ] V n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (Fin.castSucc a)).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)).toContinuousLinearMap)

theorem headL_apply {n : ℕ} (v : V (n + 1)) (a : Fin n) : headL n v a = v (Fin.castSucc a) := rfl

variable {M : Type} [TopologicalSpace M]

end GlobalTheory.LocFub
