import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TelescopingCoordinateDifference

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.telescoping_coordinate_difference : ∀ (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α), F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  exact @GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions
