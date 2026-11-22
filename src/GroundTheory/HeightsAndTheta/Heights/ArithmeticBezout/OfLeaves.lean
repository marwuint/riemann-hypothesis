import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

end GroundTheory.Heights₂.Heights
