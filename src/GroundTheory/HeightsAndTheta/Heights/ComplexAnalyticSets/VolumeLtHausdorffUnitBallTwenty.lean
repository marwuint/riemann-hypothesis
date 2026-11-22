import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory Measure Metric Module

open scoped ENNReal

noncomputable section

namespace AreaLinear

theorem statement_iff :
    GroundTheory.Heights₂.Heights.AreaLinear.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.Statement :=
  Iff.rfl

end AreaLinear

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
