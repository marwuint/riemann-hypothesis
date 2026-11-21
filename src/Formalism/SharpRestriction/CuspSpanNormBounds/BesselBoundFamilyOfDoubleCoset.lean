import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₄

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' UH (Hpk k r))

end Formalism.MainNotions.BridgeLemma₄
