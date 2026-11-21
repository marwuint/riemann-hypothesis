import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistenceLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain NumberField.InfinitePlace.Completion

section BaseChange

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable (R : Type*) [Field R] [Algebra K R]

instance isQuadraticExtension_tensor : Algebra.IsQuadraticExtension R (R ⊗[K] E) where
  finrank_eq_two' := by
    rw [Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two]

variable {R}

end BaseChange

end GroundTheory.Automorphic
