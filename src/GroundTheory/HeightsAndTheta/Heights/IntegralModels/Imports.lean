import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem Dominates.equiv (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] (V : Subring K) :
    GroundTheory.Heights₂.Heights.Model.Dominates A V ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.Dominates A V :=
  Iff.rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
