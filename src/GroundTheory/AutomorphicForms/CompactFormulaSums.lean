import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.TraceFormulaGeometric
import GroundTheory.AutomorphicForms.TraceFormulaCentralizer
import GroundTheory.AutomorphicForms.TraceFormulaWeil

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl

end UnitaryRep

namespace RightCosetSpace

end RightCosetSpace

end

end GroundTheory.Automorphic
