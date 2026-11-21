import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
