import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  exact @GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU
