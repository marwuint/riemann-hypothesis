import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_charpoly_pow_eq_map_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (M : Matrix (Fin n) (Fin n) k), (Matrix.charpoly (M ^ r)).roots = (Matrix.charpoly M).roots.map (· ^ r) := by
  exact @GlobalTheory.CharpolyPow.roots_charpoly_pow
