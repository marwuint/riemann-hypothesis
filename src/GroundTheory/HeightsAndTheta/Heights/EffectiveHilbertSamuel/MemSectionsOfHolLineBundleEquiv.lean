import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Objects
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HolLineBundleToAltTransition

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal

noncomputable section

namespace TranslateEq

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem jac_eq_jacDet (j k : Fin A.n) (x : X) : jac A j k x = jacDet A j k x := rfl

theorem twist_g (L₂ L : HolLineBundle A) (m : ℕ) (j k : Fin A.n) (x : X) :
    (twist L₂.toIndefiniteRowSideFullHecke L.toIndefiniteRowSideFullHecke m).g j k x = L₂.g j k x * L.g j k x ^ m := rfl

end TranslateEq

end

end GroundTheory.Heights₂.Heights.EffectiveHS
