import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := GlobalTheory.ZarhinFam.zW_symm_posDef
