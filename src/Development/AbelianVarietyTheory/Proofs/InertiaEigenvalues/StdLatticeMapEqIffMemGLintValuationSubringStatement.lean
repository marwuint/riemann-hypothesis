import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubring
import Formalism.SatakeDualWeyl.Statement

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  exact @GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint
