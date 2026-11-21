import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)

noncomputable section

namespace OneBlockPoints

section OfStandard

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem evalCone_eq {N : ℕ} (z : Cone (fun _ : Unit ↦ N) ℂ) (f : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :
    evalCone z f = eval₂Hom (Int.castRingHom ℂ) (fun v ↦ z v.1 v.2) f := rfl

end OfStandard

end OneBlockPoints

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
