import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesCoefficientsCuspidal : Prop := GlobalTheory.Dec.CoefCusp

theorem discreteSeriesCoefficientsCuspidal_iff : DiscreteSeriesCoefficientsCuspidal ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ →
      ∀ u v : H, IsKFin ε σ u → IsKFin ε σ v →
      ∀ W : Submodule ℂ (Fin n → ℂ), IsIsoC ε W →
      ∀ ν : @Measure (UJ ε) (borel (UJ ε)), @IsHaarSub (UJ ε) _ _ (borel (UJ ε)) (NW ε W) ν →
      ∀ x y : UJ ε,
        @Integrable ℂ _ _ (UJ ε) (borel (UJ ε)) (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) ν ∧
          @integral (UJ ε) ℂ _ _ (borel (UJ ε)) ν (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) = 0 :=
  Iff.rfl

namespace CoefficientsCuspidal

end CoefficientsCuspidal

end GlobalTheory.Published
