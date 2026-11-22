import Mathlib

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace PI.WeilQuotMeas

def WqUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ρ ρ' : Measure (G ⧸ H), ρ ≠ 0 →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
      ∃ c : ℝ≥0∞, ρ' = c • ρ

end PI.WeilQuotMeas
