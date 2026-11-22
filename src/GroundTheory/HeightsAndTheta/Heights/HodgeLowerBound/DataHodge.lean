import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Example
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Subbundle

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

def IsSubbundle (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (F : Submodule Ω E)
    (r : ℕ) : Prop :=
  ∀ c : (k : K) → ι k, segreCoord y c ≠ 0 →
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
      (∀ l, a l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, a l * f l = 1 ∧
      ∀ l, f l ≠ 0 → ∃ b : Fin N → E, IsFrameOver y W c (f l) b ∧
        Submodule.span Ω (b '' {i | (i : ℕ) < r}) = F

end Subbundle

structure ComponentDataHodge (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type)
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] extends ComponentData II Ψ K ι Ω E where

  F : ∀ τ, Submodule Ω (E τ)
  hodge : ∀ τ, IsSubbundle y (W τ) (F τ) j

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
