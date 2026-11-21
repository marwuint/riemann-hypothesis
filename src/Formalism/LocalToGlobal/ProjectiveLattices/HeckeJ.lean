import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace HeckeJ

open scoped TensorProduct

section Gen

variable {L : Type*} [Field L] (σ₀ : L →+* ℂ) {WL : Type*} [AddCommGroup WL] [Module L WL]
  {H F : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup F] [Module ℂ F]
  (j : WL →ₛₗ[σ₀] H) (em : H →ₗ[ℂ] F) (TF : F →ₗ[ℂ] F) (c : ℂ)

def IsHkJ (T : WL →ₗ[L] WL) : Prop := ∀ x, em (j (T x)) = c • TF (em (j x))

variable {σ₀ j em TF c}

variable (σ₀ j em TF c)

variable {σ₀ j em TF c}

end Gen

end HeckeJ

end Formalism.L2.Pj
