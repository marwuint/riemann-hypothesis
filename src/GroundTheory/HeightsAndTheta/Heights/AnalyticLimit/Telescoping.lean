import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

theorem ell_anti {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' :=
  Real.log_le_log (inv_pos.2 (lt_of_lt_of_le ht' htt)) (inv_anti₀ ht' htt)

namespace System

end System

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
