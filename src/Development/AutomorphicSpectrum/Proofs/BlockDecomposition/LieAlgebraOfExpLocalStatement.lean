import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_of_exp_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧ ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  exact @GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra
