import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueLat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section FrameGeneric

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

def IsFrameAt (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E) (h : Ω) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, h ^ n • e ∈ M) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, h ^ n * a q ∈ A) ∧ e = ∑ q, a q • b q

end FrameGeneric

end GroundTheory.Heights₂.Heights.Model
