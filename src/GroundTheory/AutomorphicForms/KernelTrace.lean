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

theorem measurable_of_continuous_compactProd {Y β : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  let : UniformSpace Y := uniformSpaceOfCompactR1
  exact measurable_of_continuous_prod hk

variable (μ : Measure X) [IsFiniteMeasure μ]

theorem memLp_contKernel (k : C(X × X, ℂ)) : MemLp k 2 (μ.prod μ) :=
  MemLp.of_bound (measurable_of_continuous_compactProd k.continuous).aestronglyMeasurable ‖k‖
    (ae_of_all _ fun z => k.norm_coe_le_norm z)

def contKernelOp (k : C(X × X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  L2Kernel.kernelOp ((memLp_contKernel μ k).toLp k)

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

omit [T2Space X] in
theorem integrable_of_continuous_compact {f : X → ℂ} (hf : Continuous f) (ν : Measure X)
    [IsFiniteMeasure ν] : Integrable f ν := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x (mem_univ x))

namespace MeasurablePartition

end MeasurablePartition

end Diagonal

namespace MeasurablePartition

end MeasurablePartition

end

end GroundTheory.Automorphic
