import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((φ (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
