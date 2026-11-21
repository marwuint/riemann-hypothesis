import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ULogBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def hodgeInner (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) : ℝ :=
  ∑ τ, 2 * ‖D.herm.emb τ D.herm.ξ‖ *
    (∑ a, starRingEnd ℂ (((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (v b)) a) *
      ((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (w b)) a).re

end FullerData

namespace UnitaryIsotropicLineExample

end UnitaryIsotropicLineExample

end GroundTheory.Heights₂.Heights.NineStatements
