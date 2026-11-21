import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDimensionalBaseSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

end SlopeTestRemainingChoices

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
