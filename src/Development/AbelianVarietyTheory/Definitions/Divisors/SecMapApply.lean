import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.LinPair

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k]

section Abstract

variable {G H Y : Type} [Group G] [Group H]

def secMap (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) : (Y → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.pi fun h => l ∘ₗ om (1, h)

theorem secMap_apply (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) (h : H) :
    secMap om l φ h = l (om (1, h) φ) := rfl

end Abstract

end GlobalTheory.LinPair

end
