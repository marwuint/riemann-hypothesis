import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace Formalism.HermitianLattices.GL2b2

def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) ≠ 0)

end Formalism.HermitianLattices.GL2b2
