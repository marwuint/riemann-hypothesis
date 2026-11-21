import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm

open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm
