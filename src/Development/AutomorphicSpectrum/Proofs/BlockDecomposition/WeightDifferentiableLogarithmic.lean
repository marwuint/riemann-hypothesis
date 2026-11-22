import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.MatrixMulApply

noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.DInt2.DerivW

def cf (i j : Fin 2) : M22 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

theorem cf_apply (i j : Fin 2) (X : M22) : cf i j X = X i j := rfl

end GlobalTheory.CompanionTheory.DInt2.DerivW

