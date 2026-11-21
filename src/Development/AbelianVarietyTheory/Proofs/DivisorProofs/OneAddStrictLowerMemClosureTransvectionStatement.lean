import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictLower_mem_closure_transvection' : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  exact @GlobalTheory.one_add_strictLower_mem_closure_transvection
