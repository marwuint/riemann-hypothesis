import Mathlib
import GroundTheory.AutomorphicForms.TraceNormComp
import GroundTheory.AutomorphicForms.FinePartition
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel

namespace GroundTheory.Automorphic

open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

section Kernel

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

variable (μ : Measure X) [IsFiniteMeasure μ]

end Kernel

theorem Lp.coeFn_finsetSum {α E ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (s : Finset ι) (F : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E p μ] with x hx
    simp only [Finset.sum_empty]
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

namespace MeasurablePartition

end MeasurablePartition

section Diagonal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

namespace MeasurablePartition

end MeasurablePartition

end Diagonal

namespace MeasurablePartition

end MeasurablePartition

end

end GroundTheory.Automorphic
