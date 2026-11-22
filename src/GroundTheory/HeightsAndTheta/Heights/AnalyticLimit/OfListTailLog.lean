import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLogSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem GreenMassStep.full : GreenMassStep.Statement := GreenMassStep.proof

theorem GreenMassReplace.full : GreenMassReplace.Statement := GreenMassReplace.proof

theorem GreenMassError.full : GreenMassError.Statement := GreenMassError.proof

theorem UniformIntegrability.full : UniformIntegrability.Statement :=
  UniformIntegrability.of_greenMass GreenMassStep.full GreenMassReplace.full GreenMassError.full

theorem ListTailLog.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := GroundTheory.Heights₂.Heights.AnalyticLimit.ListTailLog.proof hE hM hC hS

end GroundTheory.Heights₂.Heights.AnalyticLimit
