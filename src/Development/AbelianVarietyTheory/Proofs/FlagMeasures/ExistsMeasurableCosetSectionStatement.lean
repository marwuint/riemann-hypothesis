import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSection
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_coset_section' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G), IsClosed (L : Set G) → ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  exact @GlobalTheory.exists_measurable_coset_section
