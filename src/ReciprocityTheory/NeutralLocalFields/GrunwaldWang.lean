import Mathlib

open NumberField IsDedekindDomain

namespace Neutral.GrunwaldWang

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

def IsComplexConjugationAt (w : InfinitePlace K) (c : Ω ≃ₐ[K] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap K Ω)) = w

end Neutral.GrunwaldWang
