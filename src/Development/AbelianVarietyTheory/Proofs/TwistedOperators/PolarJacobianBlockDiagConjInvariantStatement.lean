import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJacobian_blockDiag_conj_invariant : ∀ (p q : ℕ) (k k' Y : Mat p q), k * k' = 1 → IsKC k → IsKC k' → polJ (k * Y * k') = polJ Y := by
  exact @GlobalTheory.PolarU.Conj.polJ_conj
