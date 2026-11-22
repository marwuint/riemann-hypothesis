import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionL2NormSq
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace HolLineBundle

def toIndefiniteRowSideFullHecke (L : HolLineBundle A) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A where
  g := L.g
  holo := L.holo
  ne_zero := L.ne_zero
  cocycle j k l x hx := (L.cocycle j k l x hx).symm

end HolLineBundle

namespace Weight

variable {L : HolLineBundle A}

end Weight

variable {L : HolLineBundle A}

variable [MeasurableSpace X] [BorelSpace X]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
