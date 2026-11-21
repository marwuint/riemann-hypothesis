import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))

def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))

end Formalism.HermitianLattices.GL2a2
