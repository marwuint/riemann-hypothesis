import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u u' v v' w

section Objects

def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) : Prop :=
  ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
