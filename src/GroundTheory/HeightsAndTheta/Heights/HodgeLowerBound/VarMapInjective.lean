import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsPlueckerCoord

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagModelAlt

section Defs

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def stepTw {N : ℕ} (i : Fin (N - 1)) : Fin N := Fin.castLE (Nat.sub_le N 1) i

@[simp] theorem stepTw_val {N : ℕ} (i : Fin (N - 1)) : ((stepTw i : Fin N) : ℕ) = i := rfl

structure Match {D : ComponentDataHodge II Ψ K ι Ω E} (Pl : PlueckerData D.toComponentData)
    (P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D) : Prop where
  twist : ∀ τ i, Pl.bdeg τ i = P.b
  M_eq : ∀ τ i, Pl.M τ i = P.M τ (stepTw i)
  gen_eq : ∀ τ (i : Fin (D.N - 1)) m (v : Fin ((i : ℕ) + 1) → E τ),
    Pl.gen τ i m (exteriorPower.ιMulti Ω _ v) = P.gen τ (stepTw i) (Fin.cast (M_eq τ i) m) v

variable {D : ComponentDataHodge II Ψ K ι Ω E} {Pl : PlueckerData D.toComponentData}
  {P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D}

end Defs

section Inhabitant

open Line

abbrev linePlData : PlueckerData lineDataHodgeZero.toComponentData := linePl zeroSystem fun _ _ => le_rfl

end Inhabitant

end FlagModelAlt

end GroundTheory.Heights₂.Heights.LowerBoundFree
