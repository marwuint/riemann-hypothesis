import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by
  exact @GlobalTheory.norm_pos_of_totallyPositive
