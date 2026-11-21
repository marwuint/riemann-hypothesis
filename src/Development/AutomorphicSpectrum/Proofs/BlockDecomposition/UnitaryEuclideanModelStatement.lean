import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_euclidean_model : ∀ {n : ℕ} (E : KMod n), ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) (ρ' : Matrix.unitaryGroup (Fin n) ℂ →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))), Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  exact @GlobalTheory.CompanionTheory.RealCount.dualRep_exists
