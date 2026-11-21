import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseBoundedHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightComparison.main : HeightComparison.Statement := heightComparison

theorem DenseBoundedHeight.main : DenseBoundedHeight.Statement := denseBoundedHeight

theorem SlopeMaxExtension.main : SlopeMaxExtension.Statement := slopeMaxExtension

end GroundTheory.Heights₂.Heights
