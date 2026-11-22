import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x4
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module

section Lin
variable {K : Type*} [Field K]

variable {V A A' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
  [AddCommGroup A'] [Module K A']

def kerPart (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (j : A' →ₗ[K] V) :
    A' →ₗ[K] LinearMap.ker π :=
  LinearMap.codRestrict _ (j - σ ∘ₗ π ∘ₗ j) (fun x => by simp [hσ])

end Lin
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P.S3x4
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.S3x4
end Formalism.FourierDecayAlt.P.S3x4

namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
