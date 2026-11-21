import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagComplexPointsOverX

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def flZIncr (Ψ : Type) (N : ℕ) :
    (Σ q : Ψ × Fin (N - 1), IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZBlk Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨p.1, ⟨p.2.1.orderEmbOfFin p.2.2, (p.2.1.orderEmbOfFin p.2.2).strictMono⟩⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
