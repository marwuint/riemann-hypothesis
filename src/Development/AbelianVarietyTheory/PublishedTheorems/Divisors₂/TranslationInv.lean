import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormPoint

set_option autoImplicit false

noncomputable section

open Matrix Set
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm

def IsDatum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ) : Prop :=
  IsPeriodMap B τ ∧ IsLat M ∧ IsFactor B τ M j ∧ IsMetric B τ M j h

end GlobalTheory.TorsionForm
