import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x6
open Module

structure Inv {K : Type} [Field K] (σ : K →+* K) : Prop where
  invol : ∀ x, σ (σ x) = x
  norm_surj : ∀ c, σ c = c → ∃ y, σ y * y = c
  trace_one : ∃ l, l + σ l = 1

variable {K : Type} [Field K] {σ : K →+* K}

def Herm {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) : Prop :=
  ∀ u v, σ (h u v) = h v u

section A1
variable {V : Type} [AddCommGroup V] [Module K V]

end A1

end Formalism.FourierDecayAlt.P.S3x6

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
