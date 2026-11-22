import Mathlib
import GroundTheory.AutomorphicForms.KernelTrace

namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal

noncomputable section

section Uniform

variable {X : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

end Uniform

section Comp

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

end Comp

end

end GroundTheory.Automorphic
