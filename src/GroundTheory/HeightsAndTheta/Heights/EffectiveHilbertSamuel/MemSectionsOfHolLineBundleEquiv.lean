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

end TranslateEq

end

end GroundTheory.Heights₂.Heights.EffectiveHS
