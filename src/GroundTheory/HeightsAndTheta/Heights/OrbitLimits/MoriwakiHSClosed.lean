import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

end GroundTheory.Heights₂.Heights.Targets
