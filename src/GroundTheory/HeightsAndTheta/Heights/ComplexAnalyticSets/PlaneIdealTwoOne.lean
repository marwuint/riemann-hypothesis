import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

theorem mdisc_const_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
