import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PObjectsDivCycleGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace RecQOfRecursion

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)

variable {n : ℕ}

open Classical in

theorem divCycle_apply (P : Ideal (MRing (PBlk n))) (s : MRing (PBlk n)) (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W = if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0 :=
  rfl

end RecQOfRecursion

end

end GroundTheory.Heights₂.Heights
