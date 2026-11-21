import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartVanishing

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def evalHom {F : Type*} [CommRing F] (z : Cone n F) : MvPolynomial (Coord n) ℤ →+* F :=
  eval₂Hom (Int.castRingHom F) fun v : Coord n ↦ z v.1 v.2

omit [Fintype ι] [DecidableEq ι] in
theorem evalHom_apply {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalHom z f = evalCone z f := rfl

end ChartVanishing

end

end GroundTheory.Heights₂.Heights
