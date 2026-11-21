import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

variable {D : ℕ} {U : Type} [TopologicalSpace U]

def jac (A : FinHolAtlas D U) (j k : Fin A.n) (x : U) : ℂ :=
  LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) (A.chart j x) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
