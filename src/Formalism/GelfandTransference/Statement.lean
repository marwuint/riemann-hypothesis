import Mathlib
import Formalism.NormUnitaryBounds.Statement

open MvPolynomial Finset

noncomputable section

namespace Formalism.HadamardInequality

def Hadamard : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ), ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2

def HadamardMax : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) (M : ℝ), (∀ i j, ‖A i j‖ ≤ M) →
    ‖A.det‖ ^ 2 ≤ ((ρ : ℝ) * M ^ 2) ^ ρ

end Formalism.HadamardInequality
