import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCChartGradient

theorem u_eq (D : PeriodChartData) :
    D.u = fun q => logDetGram (D.Y q.1) (D.f q) := rfl

end MCChartGradient

end

end GroundTheory.Heights₂.Heights
