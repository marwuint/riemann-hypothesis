import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[reassoc (attr := simp)]
lemma toOpen_homOfLE (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) {m : ℤ} (hm : IsUnit (m : R))
    (h : W ≤ invOpen f m) : toOpen f R W hW ≫ X.homOfLE h = toInvOpen f R m hm := by
  rw [← cancel_mono (invOpen f m).ι]
  simp [Scheme.homOfLE_ι]

end

end GroundTheory.Heights₂.Heights.Model
