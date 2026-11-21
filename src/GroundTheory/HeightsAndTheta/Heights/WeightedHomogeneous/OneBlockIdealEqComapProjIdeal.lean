import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem pullFS_metric (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z =
      (HermLine.standard (fun _ : Unit ↦ n k₀)).metric (Heights.projBlock k₀ z) := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
