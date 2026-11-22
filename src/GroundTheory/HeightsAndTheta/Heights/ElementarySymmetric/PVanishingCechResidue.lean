import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ZeroSetFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

end

end GroundTheory.Heights₂.Heights.KeyFormula
