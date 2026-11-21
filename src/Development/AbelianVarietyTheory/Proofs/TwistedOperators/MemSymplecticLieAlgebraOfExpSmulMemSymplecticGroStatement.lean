import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  exact @GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup
