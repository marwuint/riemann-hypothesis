import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

def relabelBlocks {K K' : Type} {ι : K → Type} {ι' : K' → Type} (ε : K ≃ K')
    (h : ∀ k, ι k = ι' (ε k)) : (Σ k, ι k) ≃ (Σ k', ι' k') :=
  Equiv.sigmaCongr ε fun k => Equiv.cast (h k)

end GroundTheory.Heights₂.Heights
