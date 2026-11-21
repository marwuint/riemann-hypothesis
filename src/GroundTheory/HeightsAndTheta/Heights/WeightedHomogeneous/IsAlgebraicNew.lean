import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace AddBlockDimension

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)

abbrev plusMap : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Option ι) P.FunField := D.extMap

theorem ker_plusMap : RingHom.ker (plusMap D) = D.extIdeal := rfl

end AddBlockDimension

end

end GroundTheory.Heights₂.Heights
