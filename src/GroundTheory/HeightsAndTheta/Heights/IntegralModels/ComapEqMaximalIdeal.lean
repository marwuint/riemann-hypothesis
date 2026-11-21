import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem blowUpChart_eq_model {A K : Type} [CommRing A] [Field K] [Algebra A K] {n : ℕ}
    (x : Fin n → A) (i : Fin n) :
    _root_.GroundTheory.Heights₂.Heights.Model.blowUpChart K x i = blowUpChart A K x i := rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
