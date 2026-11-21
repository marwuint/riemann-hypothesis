import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Covolume

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module ZSpan NumberField

noncomputable section

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]

omit [MeasurableSpace V] [BorelSpace V] in

theorem finite_lattice_closedBall (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : V) r)
    (s := (L : Set V)) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩

variable [IsZLattice ℝ L]

end Euclidean

end

end GroundTheory.Heights₂.Heights
