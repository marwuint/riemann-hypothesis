import Mathlib

open MeasureTheory Metric

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  {κ : Type} [Fintype κ] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)]
  (μ : Measure (κ → K)) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)

private noncomputable def four (f : (κ → K) → ℂ) (y : κ → K) : ℂ :=
  ∫ x, ψ (dotProduct x y) * f x ∂μ

variable {d : K} (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
include hd

end

