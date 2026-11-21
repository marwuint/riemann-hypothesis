import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

namespace HtBoundary

section Objects

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

variable (Em) in

def logDerivL : ℝ :=
  limUnder (𝓝[>] (1 : ℝ)) fun σ : ℝ =>
    (logDeriv (dedekindZeta Em) σ - logDeriv (dedekindZeta (maximalRealSubfield Em)) σ).re

variable (Em) in

def La (B : ℕ) : ℝ := Real.log (B * rootDiscr Em) + |logDerivL Em|

end Objects

namespace Flat

end Flat

end HtBoundary

end GroundTheory.Heights₂.Heights.NineStatements
