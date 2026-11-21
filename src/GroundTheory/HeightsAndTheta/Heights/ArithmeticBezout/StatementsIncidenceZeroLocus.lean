import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncidenceZeroLocus.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal Q →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] (v : Fin k × Fin n → Ω),
      (∀ g ∈ incIdeal Q k, aeval v g = 0) →
        ∃ y : Fin n → Ω, y ≠ 0 ∧ (∀ q ∈ Q, aeval y q = 0) ∧ ∀ i, ∑ j, v (i, j) * y j = 0

end

end GroundTheory.Heights₂.Heights
