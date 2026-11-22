import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.MatrixMulApply

open Ad3.LR

noncomputable section

namespace GlobalTheory.CompanionTheory.DInt2.Drho

def pr (i j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

theorem pr_apply (i j : Fin 2) (h : M22) : pr i j h = (h i j : ℂ) := rfl

end GlobalTheory.CompanionTheory.DInt2.Drho
