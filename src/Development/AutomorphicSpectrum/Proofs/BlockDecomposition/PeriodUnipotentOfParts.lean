import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Z2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PerUAssembled

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        have : Matrix.of (X + Y) = Matrix.of X + Matrix.of Y := rfl
        rw [this, Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        have : Matrix.of (c • X) = c • Matrix.of X := rfl
        rw [this, Matrix.smul_mul]
        rfl
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

theorem rtEquiv_apply (g : GL (Fin 3) ℝ) (X : M23) :
    rtEquiv g X = Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)) := rfl

end GlobalTheory.CompanionTheory.PerUAssembled
