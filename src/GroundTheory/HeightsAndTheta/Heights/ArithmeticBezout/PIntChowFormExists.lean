import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem chowFormExists : ChowFormExists.Statement :=
  ChowFormExists.of_affineChartTrdeg AffineChartTrdeg.proof

end ObjectsChow

end GroundTheory.Heights₂.Heights
