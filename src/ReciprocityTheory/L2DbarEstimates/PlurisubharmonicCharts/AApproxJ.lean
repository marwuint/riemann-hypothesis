import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

structure CutData (Sf : Finset Y) where
  β : Y → V n → ℝ
  r1 : Y → ℝ
  r2 : Y → ℝ
  W : Y → Set Y
  smooth : ∀ P, ContDiff ℝ ∞ (β P)
  one : ∀ P, ∀ u ∈ closedBall (A.chart (A.pick P) P) (r1 P), β P u = 1
  supp : ∀ P, ∀ u, β P u ≠ 0 → u ∈ closedBall (A.chart (A.pick P) P) (r2 P)
  sub : ∀ P ∈ Sf, closedBall (A.chart (A.pick P) P) (r2 P) ⊆
    (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' W P
  disj : ∀ P ∈ Sf, ∀ Q ∈ Sf, P ≠ Q → Disjoint (W P) (W Q)

variable {A}

namespace CutData

end CutData

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
