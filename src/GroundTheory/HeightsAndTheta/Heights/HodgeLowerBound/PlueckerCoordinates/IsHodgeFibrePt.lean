import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsPlueckerCoord

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentDataHodge II Ψ K ι Ω E}

section FlagReg

def lastIdx (D : ComponentDataHodge II Ψ K ι Ω E) : Fin D.N :=
  ⟨D.N - 1, by have := D.two_le_N; omega⟩

end FlagReg

section Mu

def jIdx (D : ComponentDataHodge II Ψ K ι Ω E) : Fin D.N :=
  ⟨D.j - 1, by have := D.one_le_j; have := D.j_le; have := D.two_le_N; omega⟩

abbrev MuBlocks (D : ComponentDataHodge II Ψ K ι Ω E) : Type := K ⊕ (Ψ ⊕ Ψ)

def ιMu (P : PlueckerData D) : MuBlocks D → Type
  | Sum.inl k => ι k
  | Sum.inr (Sum.inl τ) => Fin (P.M τ (jIdx D))
  | Sum.inr (Sum.inr τ) => Fin (P.M τ (lastIdx D))

instance instFintypeιMu (P : PlueckerData D) : ∀ k, Fintype (ιMu P k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr (Sum.inl τ) => inferInstanceAs (Fintype (Fin (P.M τ (jIdx D))))
  | Sum.inr (Sum.inr τ) => inferInstanceAs (Fintype (Fin (P.M τ (lastIdx D))))

def SB (D : ComponentDataHodge II Ψ K ι Ω E) (B : ℕ) : Finset ℕ := D.S.filter (· ≤ B)

end Mu

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
