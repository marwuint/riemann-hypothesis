import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace AddBlockBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false

abbrev ConeField (ι Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial ι Ω)

def coneHom (y : Coord n → Ω) : MvPolynomial (Coord n) ℤ →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp (Geo.mConeMap (ι := blockIdx n) y).toRingHom

theorem coneHom_apply (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    coneHom y f = algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (Geo.mConeMap (ι := blockIdx n) y f) := rfl

variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

end AddBlockBridge

end

end GroundTheory.Heights₂.Heights
