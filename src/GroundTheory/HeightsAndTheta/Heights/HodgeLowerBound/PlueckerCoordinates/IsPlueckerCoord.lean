import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Twist

variable {Ω : Type} [Field Ω]

def twistFactor (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (b : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ (-b k)

variable {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

def IsDualSectionOver (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (c : (k : K) → ι k)
    (b : K → ℤ) {r : ℕ} (φ : E [⋀^Fin r]→ₗ[Ω] Ω) : Prop :=
  ∀ e : Fin r → E, (∀ a, e a ∈ W.lat c) → φ e * twistFactor y c b ∈ chartRing ℤ (segreCoord y) c

end Twist

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure PlueckerData (D : ComponentDataHodge II Ψ K ι Ω E) where

  b : K → ℤ

  M : Ψ → Fin D.N → ℕ
  M_ge : ∀ τ (i : Fin D.N), D.N.choose ((i : ℕ) + 1) ≤ M τ i

  gen : ∀ τ (i : Fin D.N), Fin (M τ i) → (E τ [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω)
  global : ∀ τ (i : Fin D.N) m (c : (k : K) → ι k), segreCoord D.y c ≠ 0 →
    IsDualSectionOver D.y (D.W τ) c b (gen τ i m)
  generates : ∀ τ (i : Fin D.N) (c : (k : K) → ι k), segreCoord D.y c ≠ 0 →
    ∀ φ : E τ [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω, IsDualSectionOver D.y (D.W τ) c b φ →
      ∃ a : Fin (M τ i) → Ω, (∀ m, a m ∈ chartRing ℤ (segreCoord D.y) c) ∧ φ = ∑ m, a m • gen τ i m

variable {D : ComponentDataHodge II Ψ K ι Ω E}

abbrev YBlk (D : ComponentDataHodge II Ψ K ι Ω E) : Type := K ⊕ (Ψ × Fin D.N)

def ιY (P : PlueckerData D) : YBlk D → Type
  | Sum.inl k => ι k
  | Sum.inr q => Fin (P.M q.1 q.2)

instance instFintypeιY (P : PlueckerData D) : ∀ k, Fintype (ιY P k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr q => inferInstanceAs (Fintype (Fin (P.M q.1 q.2)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
