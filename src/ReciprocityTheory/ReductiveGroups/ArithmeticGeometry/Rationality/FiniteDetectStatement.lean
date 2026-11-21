import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Submodule F (F ⊗[K] V) :=
  Submodule.span F ((fun u => (1 : F) ⊗ₜ[K] u) '' (U : Set V))

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def inclT (K₁ : IntermediateField K Ω) (V : Type*) [AddCommGroup V] [Module K V] :
    K₁ ⊗[K] V →ₗ[K₁] Ω ⊗[K] V :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K₁ Ω) (LinearMap.id : V →ₗ[K] V)

def DefinedOver (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) : Prop :=
  ∀ x : K' ⊗[K] V, c (inclT K' V x) ∈ Set.range (algebraMap K' Ω)

end Defs

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
