import Mathlib

namespace Formalism.NuclearRankWeightBounds.P

open Finset

noncomputable def sz {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) : ℝ :=
  ∑ A ∈ (univ : Finset (Fin f)).powerset, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * a ^ 2

end Formalism.NuclearRankWeightBounds.P
