import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

open NumberField

structure NormFam (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] where
  N : (K →+* ℂ) → V → ℝ
  nonneg : ∀ σ v, 0 ≤ N σ v
  eq_zero : ∀ σ v, N σ v = 0 → v = 0
  smul : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v
  add : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w

section Defs

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V]

def ProdLower (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ) : Prop :=
  ∀ f ∈ M, f ≠ 0 → -A ≤ ∑ σ : K →+* ℂ, Real.log (Nf.N σ f)

def UnifDiscrete (Nf : NormFam K V) (M : Submodule (𝓞 K) V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ M, (∀ σ, Nf.N σ f < ε) → f = 0

end Defs

def DiscOfProdLowerSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ),
    ProdLower Nf M A → UnifDiscrete Nf M

def FGOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → M.FG

end ReciprocityTheory.ChartRestriction.G.TB
